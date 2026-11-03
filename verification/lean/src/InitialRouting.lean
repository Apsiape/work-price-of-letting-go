import OwnedReadout

/-! The initial case of the operational routing argument, derived from the
actual cut-zero extension and tester gates with no schedule restrictions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.History

theorem held_initial {I : Inventory} (S : Schedule I) : held S ⟨0,by omega⟩ = ∅ := by
  ext c
  simp [held]

def initialTesterMatrix {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r) :
    Mat (Payload I × Fin r) := pureMatrix (fun x => t.initial (x.2,x.1))

def preparedTesterMatrix {I : Inventory} {S : Schedule I} {r : ℕ} (t : Tester S r) :
    Mat (Payload I × Fin r) :=
  evolve ((t.gate ⟨0,by omega⟩).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _))
    (initialTesterMatrix t)

theorem initialTesterMatrix_trace {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) : (initialTesterMatrix t).trace = 1 := by
  rw [initialTesterMatrix,pureMatrix_trace]
  have he : (∑ x : Payload I × Fin r, Complex.normSq (t.initial (x.2,x.1))) = 1 := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    simpa only [Fintype.sum_prod_type] using t.normalized
  rw [he,Complex.ofReal_one]

theorem preparedTesterMatrix_density {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) : (preparedTesterMatrix t).PosSemidef ∧ (preparedTesterMatrix t).trace = 1 :=
  evolve_density _ _ (unitary_submatrix _ (t.unitary _))
    (pureMatrix_positive _) (initialTesterMatrix_trace t)

theorem initial_contact_product {I : Inventory} {S : Schedule I} (e : Extension S)
    {r : ℕ} (t : Tester S r) : run e t 1 = zeroVisitBody e ⊗ₖ preparedTesterMatrix t := by
  have hl := e.gate_local ⟨0,by omega⟩
  rw [held_initial S] at hl
  have hD := congrArg (liftDeviceObservable e r) (local_empty_tensor I e.b (e.gate ⟨0,by omega⟩) hl)
  rw [liftDevice_body] at hD
  rw [run,dif_pos (by omega),jointGate_as_product,hD,evolve_mul]
  change evolve ((1 : Mat (Fin e.b)) ⊗ₖ
    ((t.gate ⟨0,by omega⟩).submatrix (Equiv.prodComm _ _) (Equiv.prodComm _ _)))
      (evolve (emptyBodyMatrix I e.b (e.gate ⟨0,by omega⟩) ⊗ₖ (1 : Mat (Payload I × Fin r)))
        (e.source.matrix ⊗ₖ initialTesterMatrix t)) = _
  simp only [zeroVisitBody,preparedTesterMatrix,evolve,conjTranspose_kronecker,
    ← mul_kronecker_mul,conjTranspose_one,one_mul,mul_one]

def ownedTesterMatrix (I : Inventory) (r : ℕ) (A : Finset (Fin I.count))
    (ρ : Mat (Payload I × Fin r)) : Mat (Restricted I A) :=
  partialRight (ρ.submatrix (ownershipEnvironment I r A).symm (ownershipEnvironment I r A).symm)

theorem owned_product_marginal {I : Inventory} {S : Schedule I} (e : Extension S) (r : ℕ)
    (A : Finset (Fin I.count)) (B : Mat (Fin e.b)) (ρ : Mat (Payload I × Fin r)) :
    ownedMarginal e r A (B ⊗ₖ ρ) = B ⊗ₖ ownedTesterMatrix I r A ρ := by
  ext i j
  change (∑ z : Fin r × Restricted I Aᶜ,
    B i.1 j.1 * ρ ((payloadPartition I A).symm (i.2,z.2),z.1)
      ((payloadPartition I A).symm (j.2,z.2),z.1)) = _
  exact (Finset.mul_sum _ _ _).symm

theorem first_owned_history_product {I : Inventory} {S : Schedule I} (e : Extension S)
    (h : 0 < S.visits) {r : ℕ} (t : Tester S r) :
    ownedHistory e t (⟨1,by omega⟩ : Cut S) = zeroVisitBody e ⊗ₖ
      ownedTesterMatrix I r (held S ⟨1,by omega⟩) (preparedTesterMatrix t) := by
  unfold ownedHistory
  rw [initial_contact_product,owned_product_marginal]

end ScheduleLaw.History
