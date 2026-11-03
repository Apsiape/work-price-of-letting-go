import FactoryControllerReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryDrivenProduct
open History

/-- A body product return for a zero-visit circuit is also a product return
with every coherent tester and the entire physical rest. -/
theorem product {I : Inventory} (S : Schedule I) (hS : S.visits=0) (β : ℝ) (c w r : ℕ)
    (hc : 0 < c) (hw : 0 < w) (hr : 0 < r) (ρ : Density (Fin c))
    (HC : Hamiltonian (Fin c)) (HR : Hamiltonian (Fin r)) (E : Fin w → ℝ)
    (initial nominal : Fin w) (capital : ℝ)
    (U : Mat (Fin c × (Fin w × Fin r))) (hU : IsUnitary U)
    (ω : Density (Fin w × Fin r))
    (hout : evolve U (ρ.matrix ⊗ₖ
      (pureMatrix (fun j => if j=initial then 1 else 0) ⊗ₖ gibbs β HR)) = ρ.matrix ⊗ₖ ω.matrix)
    {z : ℕ} (t : Tester S z) :
    let p := FactoryDriven.hardware S β c w r hc hw hr ρ HC HR E initial nominal capital U hU
    ∃ σ : Density ((Fin w × Fin r) × (Payload I × Fin z)),
      FactoryControllerReturn.wholeState p t=ρ.matrix ⊗ₖ σ.matrix := by
  obtain ⟨τ,hτ⟩ := FactoryCircuit.final_product S hS
    (Nat.mul_pos hc (Nat.mul_pos hw hr)) (FactoryDriven.source β hr ρ HR initial)
    (U.submatrix (FactoryDriven.split c w r) (FactoryDriven.split c w r))
    (unitary_submatrix _ hU) t
  let σ : Density ((Fin w × Fin r) × (Payload I × Fin z)) :=
    ⟨ω.matrix ⊗ₖ τ.matrix,ω.positive.kronecker τ.positive,by
      rw [trace_kronecker,ω.normalized,τ.normalized,one_mul]⟩
  refine ⟨σ,?_⟩
  change (finalState (FactoryCircuit.bodyCircuit S (Nat.mul_pos hc (Nat.mul_pos hw hr))
      (FactoryDriven.source β hr ρ HR initial)
      (U.submatrix (FactoryDriven.split c w r) (FactoryDriven.split c w r)) (unitary_submatrix _ hU)) t).submatrix
    (fun x : Fin c × ((Fin w × Fin r) × (Payload I × Fin z)) => ((FactoryDriven.split c w r).symm (x.1,x.2.1),x.2.2))
    (fun x : Fin c × ((Fin w × Fin r) × (Payload I × Fin z)) => ((FactoryDriven.split c w r).symm (x.1,x.2.1),x.2.2))= _
  rw [hτ]
  change ((evolve (U.submatrix (FactoryDriven.split c w r) (FactoryDriven.split c w r))
    ((ρ.matrix ⊗ₖ (pureMatrix (fun j => if j=initial then 1 else 0) ⊗ₖ gibbs β HR)).submatrix
      (FactoryDriven.split c w r) (FactoryDriven.split c w r))) ⊗ₖ τ.matrix).submatrix _ _ = _
  rw [evolve_submatrix_equiv,hout]
  ext i j
  simp only [submatrix_apply,kroneckerMap_apply,Equiv.apply_symm_apply,σ]
  ring

end ScheduleLaw.Blueprint.FactoryDrivenProduct
