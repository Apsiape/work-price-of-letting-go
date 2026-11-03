import FactoryPackedFormation
import FactoryReservoirEnergy
import FactorySwapEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPhysicalHamiltonian
open History FactoryRegisters

def sumH {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (A : Mat a) (B : Mat b) : Mat (a × b) :=
  A ⊗ₖ (1 : Mat b) + (1 : Mat a) ⊗ₖ B

variable {b c t1 t2 t4 : Type}
  [Fintype b] [Fintype c] [Fintype t1] [Fintype t2] [Fintype t4]
  [DecidableEq b] [DecidableEq c] [DecidableEq t1] [DecidableEq t2] [DecidableEq t4]

def work (x : ℝ) : Mat (Fin 2) := diagonal ![0,(x : ℂ)]

theorem one_prod {a z : Type} [DecidableEq a] [DecidableEq z] (i j : a × z) :
    (1 : Mat (a × z)) i j = (1 : Mat a) i.1 j.1 * (1 : Mat z) i.2 j.2 := by
  exact congrArg (fun A : Mat (a × z) => A i j) Matrix.one_kronecker_one.symm

theorem indicator_and (p q : Prop) [Decidable p] [Decidable q] :
    (if p ∧ q then (1 : ℂ) else 0) =
      (if p then (1 : ℂ) else 0) * (if q then (1 : ℂ) else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq]

/-- Full physical energy: batch, four work bits, all three retired baths,
and both zero-energy coding/reset registers. -/
def hamiltonian (H : Mat b) (H1 : Mat t1) (H2 : Mat t2) (H4 : Mat t4)
    (x1 x2 x3 x4 : ℝ) : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4)) :=
  sumH (0 : Mat c) (sumH H (sumH (work x1) (sumH (work x2)
    (sumH (work x3) (sumH (work x4) (sumH H1 (sumH H2 (sumH H4 (0 : Mat c)))))))))

theorem first_conserves (H : Mat b) (H1 : Mat t1) (H2 : Mat t2) (H4 : Mat t4)
    (x1 x2 x3 x4 : ℝ) (U : Mat (b × (Fin 2 × t1))) (hU : IsUnitary U)
    (hc : Conserves U (sumH H (sumH (work x1) H1))) :
    Conserves (FactoryPlacement.place firstFrame U)
      (hamiltonian (c:=c) H H1 H2 H4 x1 x2 x3 x4) := by
  let K := sumH (0 : Mat c) (sumH (work x2) (sumH (work x3)
    (sumH (work x4) (sumH H2 (sumH H4 (0 : Mat c))))))
  have he : hamiltonian (c:=c) H H1 H2 H4 x1 x2 x3 x4 =
      (sumH (sumH H (sumH (work x1) H1)) K).submatrix firstFrame firstFrame := by
    ext ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
      ⟨code',batch',v1,v2,v3,v4,bath1',bath2',bath4',fresh'⟩
    simp only [hamiltonian,sumH,K,submatrix_apply,firstFrame,Equiv.coe_fn_mk,
      add_apply,kroneckerMap_apply,Matrix.zero_apply,Matrix.one_apply,Prod.mk.injEq,indicator_and,zero_mul,zero_add,mul_zero,add_zero]
    ring
  rw [he]
  exact FactoryPlacement.conserves firstFrame U _ K hU hc

theorem second_conserves (H : Mat b) (H1 : Mat t1) (H2 : Mat t2) (H4 : Mat t4)
    (x1 x2 x3 x4 : ℝ) (U : Mat (c × (Fin 2 × t2))) (hU : IsUnitary U)
    (hc : Conserves U (sumH (0 : Mat c) (sumH (work x2) H2))) :
    Conserves (FactoryPlacement.place secondFrame U)
      (hamiltonian H H1 H2 H4 x1 x2 x3 x4) := by
  let K := sumH H (sumH (work x1) (sumH (work x3)
    (sumH (work x4) (sumH H1 (sumH H4 (0 : Mat c))))))
  have he : hamiltonian H H1 H2 H4 x1 x2 x3 x4 =
      (sumH (sumH (0 : Mat c) (sumH (work x2) H2)) K).submatrix secondFrame secondFrame := by
    ext ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
      ⟨code',batch',v1,v2,v3,v4,bath1',bath2',bath4',fresh'⟩
    simp only [hamiltonian,sumH,K,submatrix_apply,secondFrame,Equiv.coe_fn_mk,
      add_apply,kroneckerMap_apply,Matrix.zero_apply,Matrix.one_apply,Prod.mk.injEq,indicator_and,zero_mul,zero_add,mul_zero,add_zero]
    ring
  rw [he]
  exact FactoryPlacement.conserves secondFrame U _ K hU hc

theorem fourth_conserves (H : Mat b) (H1 : Mat t1) (H2 : Mat t2) (H4 : Mat t4)
    (x1 x2 x3 x4 : ℝ) (U : Mat (c × (Fin 2 × t4))) (hU : IsUnitary U)
    (hc : Conserves U (sumH (0 : Mat c) (sumH (work x4) H4))) :
    Conserves (FactoryPlacement.place fourthFrame U)
      (hamiltonian H H1 H2 H4 x1 x2 x3 x4) := by
  let K := sumH H (sumH (work x1) (sumH (work x2)
    (sumH (work x3) (sumH H1 (sumH H2 (0 : Mat c))))))
  have he : hamiltonian H H1 H2 H4 x1 x2 x3 x4 =
      (sumH (sumH (0 : Mat c) (sumH (work x4) H4)) K).submatrix fourthFrame fourthFrame := by
    ext ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
      ⟨code',batch',v1,v2,v3,v4,bath1',bath2',bath4',fresh'⟩
    simp only [hamiltonian,sumH,K,submatrix_apply,fourthFrame,Equiv.coe_fn_mk,
      add_apply,kroneckerMap_apply,Matrix.zero_apply,Matrix.one_apply,Prod.mk.injEq,indicator_and,zero_mul,zero_add,mul_zero,add_zero]
    ring
  rw [he]
  exact FactoryPlacement.conserves fourthFrame U _ K hU hc

theorem decoder_conserves (H : Mat b) (H1 : Mat t1) (H2 : Mat t2) (H4 : Mat t4)
    (x1 x2 x3 x4 : ℝ) (V : Mat c) (hV : IsUnitary V) :
    Conserves (FactoryPlacement.place resetFrame V)
      (hamiltonian H H1 H2 H4 x1 x2 x3 x4) := by
  let J := sumH H <| sumH (work x1) <| sumH (work x2) <| sumH (work x3) <|
    sumH (work x4) <| sumH H1 <| sumH H2 H4
  let K := J ⊗ₖ (1 : Mat c)
  have he : hamiltonian H H1 H2 H4 x1 x2 x3 x4 =
      (sumH (0 : Mat c) K).submatrix resetFrame resetFrame := by
    ext ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
      ⟨code',batch',v1,v2,v3,v4,bath1',bath2',bath4',fresh'⟩
    simp only [hamiltonian,sumH,K,J,submatrix_apply,resetFrame,Equiv.coe_fn_mk,
      add_apply,kroneckerMap_apply,Matrix.zero_apply,Matrix.one_apply,Prod.mk.injEq,indicator_and,
      zero_mul,zero_add,mul_zero,add_zero]
    ring
  rw [he]
  exact FactoryPlacement.conserves resetFrame V _ K hV (by simp [Conserves])

theorem reset_conserves (H : Mat b) (H1 : Mat t1) (H2 : Mat t2) (H4 : Mat t4)
    (x1 x2 x3 x4 : ℝ) :
    Conserves (resetGate (c:=c)) (hamiltonian H H1 H2 H4 x1 x2 x3 x4) := by
  let K := sumH H <| sumH (work x1) <| sumH (work x2) <| sumH (work x3) <|
    sumH (work x4) <| sumH H1 <| sumH H2 H4
  have he : hamiltonian (c:=c) H H1 H2 H4 x1 x2 x3 x4 =
      ((1 : Mat c) ⊗ₖ (K ⊗ₖ (1 : Mat c))).submatrix resetFrame resetFrame := by
    ext ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
      ⟨code',batch',v1,v2,v3,v4,bath1',bath2',bath4',fresh'⟩
    simp only [hamiltonian,sumH,K,submatrix_apply,resetFrame,Equiv.coe_fn_mk,
      add_apply,kroneckerMap_apply,Matrix.zero_apply,Matrix.one_apply,Prod.mk.injEq,indicator_and,zero_mul,zero_add,mul_zero,add_zero]
    ring
  rw [he]
  exact conserves_reindex resetFrame _ _ (FactoryReset.conserves_rest K)

/-- Every conserving stage cancels in the complete initialized circuit. -/
theorem circuit_change {e : Type} [Fintype e] [DecidableEq e] (s : c ≃ b × e)
    (H : Mat b) (H1 : Mat t1) (H2 : Mat t2) (H4 : Mat t4) (x1 x2 x3 x4 : ℝ)
    (U1 : Mat (b × (Fin 2 × t1))) (U2 : Mat (c × (Fin 2 × t2)))
    (V : Mat c) (U4 : Mat (c × (Fin 2 × t4)))
    (hu1 : IsUnitary U1) (hu2 : IsUnitary U2) (hv : IsUnitary V) (hu4 : IsUnitary U4)
    (hc1 : Conserves U1 (sumH H (sumH (work x1) H1)))
    (hc2 : Conserves U2 (sumH (0 : Mat c) (sumH (work x2) H2)))
    (hc4 : Conserves U4 (sumH (0 : Mat c) (sumH (work x4) H4)))
    (ρ : Mat (R (b:=b) (c:=c) (t1:=t1) (t2:=t2) (t4:=t4))) :
    let K := hamiltonian (c:=c) H H1 H2 H4 x1 x2 x3 x4
    let σ := evolve (FactoryPlacement.place resetFrame V)
      (evolve (FactoryPlacement.place secondFrame U2) (evolve (FactoryPlacement.place firstFrame U1) ρ))
    energy K (evolve (circuit s U1 U2 V U4) ρ)-energy K ρ =
      energy K (evolve (swapPump s) σ)-energy K σ := by
  dsimp only
  have h1 := first_conserves (c:=c) H H1 H2 H4 x1 x2 x3 x4 U1 hu1 hc1
  have h2 := second_conserves H H1 H2 H4 x1 x2 x3 x4 U2 hu2 hc2
  have h4 := fourth_conserves H H1 H2 H4 x1 x2 x3 x4 U4 hu4 hc4
  have hV := decoder_conserves H H1 H2 H4 x1 x2 x3 x4 V hv
  have hR := reset_conserves (c:=c) H H1 H2 H4 x1 x2 x3 x4
  simp only [circuit,evolve_mul]
  rw [energy_conserved _ _ _ hR,energy_conserved _ _ _ h4]
  rw [energy_conserved _ _ _ hV,energy_conserved _ _ _ h2,energy_conserved _ _ _ h1]

/-- Packing preserves the literal Hamiltonian, not merely its Gibbs state. -/
theorem work_eq (x : ℝ) : work x=diagonal (fun j : Fin 2 => if j=1 then (x : ℂ) else 0) := by
  unfold work
  congr 1
  funext j
  fin_cases j <;> simp

theorem work_packed (x1 x2 x3 x4 : ℝ) :
    (diagonal (fun j => (FactoryPacking.workEnergy x1 x2 x3 x4 j : ℂ))).submatrix
      FactoryPacking.workEquiv FactoryPacking.workEquiv =
      sumH (work x1) (sumH (work x2) (sumH (work x3) (work x4))) := by
  rw [submatrix_diagonal_equiv]
  simp only [sumH,work_eq,FactoryGibbs.diagonal_sum]
  congr 1
  funext j
  simp only [FactoryPacking.workEnergy,Function.comp_apply,Equiv.symm_apply_apply,
    Complex.ofReal_add]
  split_ifs <;> (try simp_all) <;> ring

theorem body_in_frame {I : Inventory} {S : Schedule I} {β : ℝ}
    (p : Driven S β) {a : Type} [Fintype a] [DecidableEq a]
    (e : a ≃ Fin p.c × (Fin p.w × Fin p.r)) :
    p.bodyHamiltonian.submatrix (e.trans p.split.symm) (e.trans p.split.symm) =
      (sumH p.HC.matrix (sumH (diagonal (fun j => (p.batteryEnergy j : ℂ)))
        p.HR.matrix)).submatrix e e := by
  ext i j
  change (sumH p.HC.matrix (sumH (diagonal (fun j => (p.batteryEnergy j : ℂ))) p.HR.matrix))
    (p.split (p.split.symm (e i))) (p.split (p.split.symm (e j))) = _
  rw [p.split.apply_symm_apply,p.split.apply_symm_apply]
  rfl

theorem packed {d m D r1 r2 r4 : ℕ} (hd : 0 < d) (hm : 0 < m) (hD : 0 < D)
    (h1 : 0 < r1) (h2 : 0 < r2) (h4 : 0 < r4) (β : ℝ) (hβ : β ≠ 0)
    (τ q : Density (Fin d)) (hq : q.matrix.PosDef)
    (H1 : Hamiltonian (Fin r1)) (H2 : Hamiltonian (Fin r2)) (H4 : Hamiltonian (Fin r4))
    (x1 x2 x3 x4 : ℝ)
    (U : Mat (Registers (Fin m → Fin d) (Fin D) (Fin r1) (Fin r2) (Fin r4)))
    (hU : IsUnitary U) :
    let F := FactoryPackedFormation.formation hd hm hD h1 h2 h4 β hβ τ q hq
      H1 H2 H4 x1 x2 x3 x4 U hU
    F.hardware.bodyHamiltonian.submatrix
      ((FactoryPacking.frame d m D r1 r2 r4).trans F.hardware.split.symm)
      ((FactoryPacking.frame d m D r1 r2 r4).trans F.hardware.split.symm) =
      hamiltonian (tensorHamiltonian (tangentHamiltonian β q) m)
        H1.matrix H2.matrix H4.matrix x1 x2 x3 x4 := by
  dsimp only
  rw [body_in_frame]
  change (sumH (0 : Mat (Fin D))
    (sumH (diagonal (fun j => (FactoryPacking.workEnergy x1 x2 x3 x4 j : ℂ)))
      (FactoryFormation.reservoir (m:=m) β q
        (FactoryPacking.auxHamiltonian (D:=D) H1 H2 H4)).matrix)).submatrix
          (FactoryPacking.frame d m D r1 r2 r4) (FactoryPacking.frame d m D r1 r2 r4) = _
  ext ⟨code,batch,w1,w2,w3,w4,bath1,bath2,bath4,fresh⟩
    ⟨code',batch',v1,v2,v3,v4,bath1',bath2',bath4',fresh'⟩
  have hw := congrArg (fun A : Mat FactoryWorkFlags.Work =>
    A (w1,w2,w3,w4) (v1,v2,v3,v4)) (work_packed x1 x2 x3 x4)
  simp only [submatrix_apply] at hw
  simp only [sumH,FactoryPacking.frame,FactoryPacking.gather,Equiv.trans_apply,
    Equiv.prodCongr_apply,Equiv.refl_apply,Prod.map_apply,Equiv.coe_fn_mk,submatrix_apply,
    FactoryFormation.reservoir,FactoryGibbs.reindexHamiltonian,FactoryGibbs.sumHamiltonian,
    FactoryTensor.hamiltonian,FactoryGibbs.tangent,FactoryPacking.auxHamiltonian,
    FiniteFlat.zeroHamiltonian,kroneckerMap_apply,add_apply,Matrix.zero_apply,
    Equiv.apply_symm_apply,Equiv.symm_apply_apply] 
  rw [hw]
  simp only [sumH,hamiltonian,add_apply,kroneckerMap_apply,Matrix.zero_apply,
    Matrix.one_apply,(FactoryFormation.reservoirSplit d m (FactoryPacking.auxSize D r1 r2 r4)).symm.injective.eq_iff,
    (FactoryPacking.auxEquiv D r1 r2 r4).injective.eq_iff,FactoryPacking.workEquiv.injective.eq_iff,
    Prod.mk.injEq,indicator_and,zero_mul,zero_add,mul_zero,add_zero]
  ring

end ScheduleLaw.Blueprint.FactoryPhysicalHamiltonian



