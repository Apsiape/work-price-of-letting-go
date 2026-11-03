import FactoryCircuit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryDriven
open History

def split (c w r : ℕ) : Fin (c*(w*r)) ≃ Fin c × (Fin w × Fin r) :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

def source (β : ℝ) {c w r : ℕ} (hr : 0<r) (ρ : Density (Fin c))
    (HR : Hamiltonian (Fin r)) (initial : Fin w) : Density (Fin (c*(w*r))) := by
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  let σ : Density (Fin w) := ⟨pureMatrix (fun j => if j=initial then 1 else 0),
    pureMatrix_positive _,by rw [pureMatrix_trace]; simp⟩
  exact ⟨(ρ.matrix ⊗ₖ (σ.matrix ⊗ₖ gibbs β HR)).submatrix (split c w r) (split c w r),
    (ρ.positive.kronecker (σ.positive.kronecker (gibbs_positive β HR))).submatrix _,by
      rw [submatrix_trace_equiv,trace_kronecker,trace_kronecker,ρ.normalized,
        σ.normalized,gibbs_trace,one_mul,one_mul]⟩

def hardware {I : Inventory} (S : Schedule I) (β : ℝ) (c w r : ℕ)
    (hc : 0<c) (hw : 0<w) (hr : 0<r) (ρ : Density (Fin c))
    (HC : Hamiltonian (Fin c)) (HR : Hamiltonian (Fin r)) (E : Fin w → ℝ)
    (initial nominal : Fin w) (capital : ℝ)
    (U : Mat (Fin c × (Fin w × Fin r))) (hU : IsUnitary U) : Driven S β where
  extension := FactoryCircuit.bodyCircuit S (Nat.mul_pos hc (Nat.mul_pos hw hr))
    (source β hr ρ HR initial) (U.submatrix (split c w r) (split c w r))
    (unitary_submatrix _ hU)
  c := c
  w := w
  r := r
  c_pos := hc
  w_pos := hw
  r_pos := hr
  split := split c w r
  controller := ρ
  HC := HC
  HR := HR
  batteryEnergy := E
  initialLevel := initial
  nominalLevel := nominal
  capital := capital
  source_product := rfl

theorem output {I : Inventory} (S : Schedule I) (hS : S.visits=0) (β : ℝ) (c w r : ℕ)
    (hc : 0<c) (hw : 0<w) (hr : 0<r) (ρ : Density (Fin c))
    (HC : Hamiltonian (Fin c)) (HR : Hamiltonian (Fin r)) (E : Fin w → ℝ)
    (initial nominal : Fin w) (capital : ℝ)
    (U : Mat (Fin c × (Fin w × Fin r))) (hU : IsUnitary U)
    {z : ℕ} (t : Tester S z) :
    let p := hardware S β c w r hc hw hr ρ HC HR E initial nominal capital U hU
    (bodyOutput p.extension t).submatrix p.split.symm p.split.symm =
      evolve U (ρ.matrix ⊗ₖ (pureMatrix (fun j => if j=initial then 1 else 0) ⊗ₖ gibbs β HR)) := by
  dsimp only [hardware]
  rw [FactoryCircuit.output S hS]
  change (evolve (U.submatrix (split c w r) (split c w r))
    ((ρ.matrix ⊗ₖ (pureMatrix (fun j => if j=initial then 1 else 0) ⊗ₖ gibbs β HR)).submatrix
      (split c w r) (split c w r))).submatrix (split c w r).symm (split c w r).symm = _
  rw [evolve_submatrix_equiv]
  ext i j
  simp only [submatrix_apply,Equiv.apply_symm_apply]

end ScheduleLaw.Blueprint.FactoryDriven
