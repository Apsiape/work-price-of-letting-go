import CacheHardwareStock
import CachePreparationEnergy
import CacheHamiltonianSplit
import CacheTerminalReset
import FactoryPhysicalHamiltonian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CachePhysicalHamiltonian
open History CacheHardware
variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

def active (F : Formation β τ q (n+1)) (service : ℝ) : Mat (ActiveRest F) :=
  diagonal (fun z => (CachePreparationEnergy.flagEnergy F service z : ℂ)) ⊗ₖ
    (1 : Mat ((Fin n → Fin d) × CacheFactoryBody.Rest F))+
  (1 : Mat (CacheClockAdvance.Registers n)) ⊗ₖ
    (tensorHamiltonian (tangentHamiltonian β q) n ⊗ₖ (1 : Mat (CacheFactoryBody.Rest F))+
      (1 : Mat (Fin n → Fin d)) ⊗ₖ CacheFactoryEnergy.helper F)

def packed (F : Formation β τ q (n+1)) (service : ℝ) : Mat (Fin (size F)) :=
  ((HC F).matrix ⊗ₖ (1 : Mat (Fin (w F) × Fin (r F)))+
    (1 : Mat (Fin (c F))) ⊗ₖ
      ((diagonal (fun j => (workEnergy F service j : ℂ))) ⊗ₖ (1 : Mat (Fin (r F)))+
        (1 : Mat (Fin (w F))) ⊗ₖ (HR F).matrix)).submatrix
          (FactoryDriven.split (c F) (w F) (r F)) (FactoryDriven.split (c F) (w F) (r F))

theorem diagonal_entry {a : Type} [DecidableEq a] (E : a → ℂ) (i j : a) :
    diagonal E i j=(if i=j then 1 else 0)*E i := by
  by_cases h : i=j <;> simp [Matrix.diagonal,h]

theorem complex_ite (p : Prop) [Decidable p] (a b : ℝ) :
    ((if p then a else b : ℝ) : ℂ)=if p then (a : ℂ) else (b : ℂ) := by
  split_ifs <;> rfl

theorem active_packed (F : Formation β τ q (n+1)) (service : ℝ) :
    (packed F service).submatrix ((bodyFrame F).trans (activeFrame F)).symm
      ((bodyFrame F).trans (activeFrame F)).symm =
        CacheTerminalReset.hamiltonian (tangentHamiltonian β q) (active F service) := by
  ext ⟨s,⟨⟨k,u,v⟩,cache,c0,w0,a0⟩,reset⟩ ⟨s',⟨⟨k',u',v'⟩,cache',c0',w0',a0'⟩,reset'⟩
  simp only [packed,submatrix_apply,Equiv.symm_trans_apply,CacheHardwareStock.split_body,
    activeFrame,Equiv.coe_fn_symm_mk,physicalFrame,Equiv.coe_fn_mk,
    Equiv.apply_symm_apply,HC,HR,FactoryGibbs.reindexHamiltonian,rawHC,rawHR,
    FactoryGibbs.sumHamiltonian,FactoryGibbs.tangent,FlatMatrix.diagonalHamiltonian,FactoryTensor.hamiltonian,
    workEnergy,CacheWorkLedger.energy,CacheWorkLedger.helperEnergy,
    CacheTerminalReset.hamiltonian,active,CachePreparationEnergy.flagEnergy,CacheFactoryEnergy.helper,
    diagonal_entry,Matrix.add_apply,kroneckerMap_apply,Equiv.symm_apply_apply,
    (Fintype.equivFin (C F)).injective.eq_iff,(Fintype.equivFin (W F)).injective.eq_iff,
    (Fintype.equivFin (R F)).injective.eq_iff,
    Matrix.one_apply,Prod.mk.injEq,FactoryPhysicalHamiltonian.indicator_and,
    Complex.ofReal_add,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_zero,Complex.ofReal_one,Complex.ofReal_natCast,Nat.cast_add,Nat.cast_one,complex_ite]
  by_cases hu : u=1 <;> by_cases hv : v=1 <;>
    simp only [hu,hv,if_true,if_false] <;> ring

theorem physical_active (F : Formation β τ q (n+1)) (service : ℝ) :
    (CacheTerminalReset.hamiltonian (tangentHamiltonian β q) (active F service)).submatrix
      (activeFrame F) (activeFrame F)=
        CachePreparationEnergy.physical F service ⊗ₖ (1 : Mat (Fin d))+
          (1 : Mat (CacheFlaggedCircuit.Physical F)) ⊗ₖ tangentHamiltonian β q := by
  ext ⟨⟨flags,batch,helper⟩,reset⟩ ⟨⟨flags',batch',helper'⟩,reset'⟩
  obtain ⟨⟨s,cache⟩,rfl⟩ := (CacheBatchSplit.split n).symm.surjective batch
  obtain ⟨⟨s',cache'⟩,rfl⟩ := (CacheBatchSplit.split n).symm.surjective batch'
  have hh := congrArg (fun M => M (s,cache) (s',cache'))
    (CacheHamiltonianSplit.matrix (n:=n) (tangentHamiltonian β q))
  simp only [submatrix_apply,Matrix.add_apply,kroneckerMap_apply] at hh
  have he : (CacheBatchSplit.split n).symm (s,cache)=(CacheBatchSplit.split n).symm (s',cache') ↔
      s=s' ∧ cache=cache' := by rw [(CacheBatchSplit.split n).symm.injective.eq_iff]; exact Prod.ext_iff
  simp only [submatrix_apply,activeFrame,Equiv.coe_fn_mk,Equiv.apply_symm_apply,
    CacheTerminalReset.hamiltonian,active,CachePreparationEnergy.physical,CacheFactoryEnergy.physical,
    diagonal_entry,Matrix.add_apply,kroneckerMap_apply,Matrix.one_apply,Prod.mk.injEq,he,
    FactoryPhysicalHamiltonian.indicator_and] at hh ⊢
  rw [hh]
  ring

theorem packed_physical (F : Formation β τ q (n+1)) (service : ℝ) :
    (packed F service).submatrix (bodyFrame F).symm (bodyFrame F).symm =
      CachePreparationEnergy.physical F service ⊗ₖ (1 : Mat (Fin d))+
        (1 : Mat (CacheFlaggedCircuit.Physical F)) ⊗ₖ tangentHamiltonian β q := by
  rw [← physical_active]
  ext i j
  have h := congrArg (fun M => M (activeFrame F i) (activeFrame F j)) (active_packed F service)
  simpa only [submatrix_apply,Equiv.symm_trans_apply,Equiv.symm_apply_apply] using h


variable {I : Inventory} {S : Schedule I}

theorem original (bare : Extension S) (ref : Density (Fin bare.b))
    (F : Formation β bare.source ref (n+1)) (service : ℝ) :
    (hardware bare ref F service).bodyHamiltonian=packed F service := rfl

end ScheduleLaw.Blueprint.CachePhysicalHamiltonian
