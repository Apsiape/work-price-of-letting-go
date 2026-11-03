import CacheControllerReturn
import CacheServiceGates
import CacheWorkLedger
import FactoryGibbsReindex
import FactoryGibbsProduct

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheHardware
open History

theorem unitary_decidable {a : Type} [Fintype a] (U : Mat a)
    (D E : DecidableEq a) (h : @IsUnitary a _ D U) : @IsUnitary a _ E U := by
  have he : D=E := Subsingleton.elim _ _
  cases he
  exact h

variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}
abbrev Physical (F : Formation β τ q (n+1)) := CacheFlaggedCircuit.Physical F × Fin d
abbrev C (F : Formation β τ q (n+1)) := CacheControllerReturn.Controller F
abbrev W (F : Formation β τ q (n+1)) := CacheWorkLedger.Work F
abbrev R (F : Formation β τ q (n+1)) := Fin d × (Fin F.aux × Fin d)
abbrev ActiveRest (F : Formation β τ q (n+1)) :=
  CacheClockAdvance.Registers n × ((Fin n → Fin d) × CacheFactoryBody.Rest F)
abbrev c (F : Formation β τ q (n+1)) := Fintype.card (C F)
abbrev w (F : Formation β τ q (n+1)) := Fintype.card (W F)
abbrev r (F : Formation β τ q (n+1)) := Fintype.card (R F)
abbrev size (F : Formation β τ q (n+1)) := c F*(w F*r F)

def physicalFrame (F : Formation β τ q (n+1)) : Physical F ≃ C F × (W F × R F) where
  toFun
    | (((k,main,aux),batch,c0,w0,a),reset) =>
      let b := CacheBatchSplit.split n batch
      (((k,b.2),c0),(main,aux,w0),(b.1,a,reset))
  invFun
    | (((k,cache),c0),(main,aux,w0),(b,a,reset)) =>
      (((k,main,aux),(CacheBatchSplit.split n).symm (b,cache),c0,w0,a),reset)
  left_inv z := by rcases z with ⟨⟨⟨k,main,aux⟩,batch,c0,w0,a⟩,reset⟩; simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by rcases z with ⟨⟨⟨k,cache⟩,c0⟩,⟨main,aux,w0⟩,b,a,reset⟩; simp only [Equiv.apply_symm_apply]

def activeFrame (F : Formation β τ q (n+1)) : Physical F ≃ Fin d × (ActiveRest F × Fin d) where
  toFun
    | ((flags,batch,helper),reset) =>
      let b := CacheBatchSplit.split n batch
      (b.1,(flags,b.2,helper),reset)
  invFun
    | (b,(flags,cache,helper),reset) =>
      ((flags,(CacheBatchSplit.split n).symm (b,cache),helper),reset)
  left_inv z := by rcases z with ⟨⟨flags,batch,helper⟩,reset⟩; simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by rcases z with ⟨b,⟨flags,cache,helper⟩,reset⟩; simp only [Equiv.apply_symm_apply]

def bodyFrame (F : Formation β τ q (n+1)) : Fin (size F) ≃ Physical F :=
  (FactoryDriven.split (c F) (w F) (r F)).trans
    ((Equiv.prodCongr (Fintype.equivFin (C F)).symm
      (Equiv.prodCongr (Fintype.equivFin (W F)).symm (Fintype.equivFin (R F)).symm)).trans
        (physicalFrame F).symm)

theorem c_pos (hd : 0<d) (F : Formation β τ q (n+1)) : 0<c F := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  letI : Nonempty (Fin F.hardware.c) := ⟨⟨0,F.hardware.c_pos⟩⟩
  exact Fintype.card_pos

theorem w_pos (F : Formation β τ q (n+1)) : 0<w F := by
  letI : Nonempty (Fin F.hardware.w) := ⟨⟨0,F.hardware.w_pos⟩⟩
  exact Fintype.card_pos

theorem r_pos (hd : 0<d) (F : Formation β τ q (n+1)) : 0<r F := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  letI : Nonempty (Fin F.aux) := ⟨⟨0,F.aux_pos⟩⟩
  exact Fintype.card_pos

theorem size_pos (hd : 0<d) (F : Formation β τ q (n+1)) : 0<size F :=
  Nat.mul_pos (c_pos hd F) (Nat.mul_pos (w_pos F) (r_pos hd F))

def controller (F : Formation β τ q (n+1)) : Density (Fin (c F)) :=
  ⟨(CacheControllerReturn.controller F).matrix.submatrix (Fintype.equivFin (C F)).symm
      (Fintype.equivFin (C F)).symm,
    (CacheControllerReturn.controller F).positive.submatrix _,by
      rw [submatrix_trace_equiv]; exact (CacheControllerReturn.controller F).normalized⟩

def rawHC (F : Formation β τ q (n+1)) : Hamiltonian (C F) :=
  FactoryGibbs.sumHamiltonian
    (FactoryGibbs.sumHamiltonian
      (FlatMatrix.diagonalHamiltonian (Fin (n+1)) (CacheClockAdvance.clockEnergy n F.debit))
      (FactoryTensor.hamiltonian (FactoryGibbs.tangent β q) n)) F.hardware.HC

def HC (F : Formation β τ q (n+1)) : Hamiltonian (Fin (c F)) :=
  FactoryGibbs.reindexHamiltonian (Fintype.equivFin (C F)).symm (rawHC F)

def rawHR (F : Formation β τ q (n+1)) : Hamiltonian (R F) :=
  FactoryGibbs.sumHamiltonian (FactoryGibbs.tangent β q)
    (FactoryGibbs.sumHamiltonian F.auxiliaryHamiltonian (FactoryGibbs.tangent β q))

def HR (F : Formation β τ q (n+1)) : Hamiltonian (Fin (r F)) :=
  FactoryGibbs.reindexHamiltonian (Fintype.equivFin (R F)).symm (rawHR F)

def initial (F : Formation β τ q (n+1)) : Fin (w F) :=
  Fintype.equivFin (W F) (CacheWorkLedger.initial F)
def nominal (F : Formation β τ q (n+1)) : Fin (w F) :=
  Fintype.equivFin (W F) (CacheWorkLedger.nominal F)
def workEnergy (F : Formation β τ q (n+1)) (service : ℝ) (j : Fin (w F)) : ℝ :=
  CacheWorkLedger.energy F service ((Fintype.equivFin (W F)).symm j)

def source (hd : 0<d) (F : Formation β τ q (n+1)) : Density (Fin (size F)) :=
  FactoryDriven.source β (r_pos hd F) (controller F) (HR F) (initial F)

def preparation (F : Formation β τ q (n+1)) : Mat (Fin (size F)) :=
  (CacheFlaggedCircuit.circuit F ⊗ₖ (1 : Mat (Fin d))).submatrix (bodyFrame F) (bodyFrame F)

theorem preparation_unitary (F : Formation β τ q (n+1)) : IsUnitary (preparation F) := by
  apply unitary_submatrix (bodyFrame F)
  have h := unitary_kron (CacheFlaggedCircuit.circuit_unitary F)
    (show IsUnitary (1 : Mat (Fin d)) by constructor <;> simp)
  exact unitary_decidable _ _ _ h

def reset (F : Formation β τ q (n+1)) : Mat (Fin (size F)) :=
  (((FactoryReset.swap (a:=Fin d) (b:=ActiveRest F)).permMatrix ℂ).submatrix
    (activeFrame F) (activeFrame F)).submatrix (bodyFrame F) (bodyFrame F)

theorem reset_unitary (F : Formation β τ q (n+1)) : IsUnitary (reset F) := by
  apply unitary_submatrix (bodyFrame F)
  apply unitary_submatrix (activeFrame F)
  exact Recorder.permutation_unitary _

variable {I : Inventory} {S : Schedule I}

def extension (bare : Extension S) (q : Density (Fin bare.b))
    (F : Formation β bare.source q (n+1)) : Extension S :=
  let base := CacheServiceGates.extension bare (size_pos bare.b_pos F)
    ((bodyFrame F).trans (activeFrame F)) (source bare.b_pos F)
  finalBodyContact (CacheServiceGates.prepare base (preparation F) (preparation_unitary F))
    (reset F) (reset_unitary F)

/-- Concrete one-source cache, bare service, signed main pump and terminal
q reset, with every factory register retained in the original Driven body. -/
def hardware (bare : Extension S) (q : Density (Fin bare.b))
    (F : Formation β bare.source q (n+1)) (service : ℝ) : Driven S β where
  extension := extension bare q F
  c := c F
  w := w F
  r := r F
  c_pos := c_pos bare.b_pos F
  w_pos := w_pos F
  r_pos := r_pos bare.b_pos F
  split := FactoryDriven.split (c F) (w F) (r F)
  controller := controller F
  HC := HC F
  HR := HR F
  batteryEnergy := workEnergy F service
  initialLevel := initial F
  nominalLevel := nominal F
  capital := faithfulRelativeEntropy (controller F).matrix (gibbs β (HC F))/β
  source_product := rfl

theorem capital_charged (bare : Extension S) (q : Density (Fin bare.b))
    (F : Formation β bare.source q (n+1)) (service : ℝ) :
    Driven.CapitalCharged (hardware bare q F service) := le_rfl

theorem nominal_debit (bare : Extension S) (q : Density (Fin bare.b))
    (F : Formation β bare.source q (n+1)) (service : ℝ) :
    Driven.nominalDebit (hardware bare q F service)=F.debit+service := by
  change workEnergy F service (initial F)-workEnergy F service (nominal F)=_
  simpa only [workEnergy,initial,nominal,Equiv.symm_apply_apply] using
    CacheWorkLedger.nominal_debit F service

end ScheduleLaw.Blueprint.CacheHardware
