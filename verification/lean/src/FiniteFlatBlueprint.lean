import FlatLadderOutput
import FlatProjection
import FlatTransport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FiniteFlat
/-- The full square and distributional statement on the explicit finite bath.
No cap/failure column is removed from the hardware. This is the main risk. -/
theorem square_ladder (β : ℝ) (hβ : 0<β) (d k L : ℕ)
    (hd : 0<d) (hk : 0<k) (hkd : k ≤ d) :
    ∃ D : Ladder β d k L,
      flatOutput (D.converter hk) = (((successRate L/k : ℝ) : ℂ) • rankProjection d k) := by
  exact ⟨constructedLadder β d k L hkd,exact_constructed_output β hβ d k L hd hk hkd⟩

/-- Coordinates for an arbitrary Hermitian rank-k projection, rather than only
a diagonal projector. The trace is the original interface's complex trace. -/
theorem projection_coordinates (d k : ℕ) (Q : Mat (Fin d)) (hQ : Q.IsHermitian)
    (hQi : Q*Q=Q) (hkd : k ≤ d) (htr : Q.trace=(k : ℂ)) :
    ∃ V : Mat (Fin d), IsUnitary V ∧ evolve V (rankProjection d k)=Q := by
  exact projection_basis d k Q hQ hQi hkd htr

/-- Transport a zero-system-Hamiltonian converter by an actual system unitary.
The bath remains a finite actual Gibbs stock. -/
theorem rotate_converter {d : ℕ} (β x : ℝ)
    (C : SupportConverter β (zeroHamiltonian d) x) (V : Mat (Fin d)) (hV : IsUnitary V) :
    ∃ D : SupportConverter β (zeroHamiltonian d) x,
      flatOutput D = evolve V (flatOutput C) := by
  exact ⟨rotatedConverter C V hV,rotated_output C V hV⟩

theorem success_budget (f : ℝ) (hf : 0<f) :
    ∃ L : ℕ, 1-f ≤ successRate L ∧ successRate L ≤ 1 := by
  obtain ⟨L,hL⟩ := exists_nat_gt (1/f)
  have hLp : 0<(L : ℝ)+1 := by positivity
  have hsmall : 1/((L : ℝ)+1)<f := by
    apply (div_lt_iff₀ hLp).mpr
    have hx := (div_lt_iff₀ hf).mp hL
    nlinarith
  refine ⟨L,?_,?_⟩
  · have he : (L : ℝ)/((L : ℝ)+1)=1-1/((L : ℝ)+1) := by field_simp; ring
    unfold successRate
    rw [he]
    linarith
  · unfold successRate
    apply (div_le_iff₀ hLp).mpr
    linarith

/-- Full assembly at the unchanged exact-flat conversion proposition. -/
theorem exact_flat {d : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (Q : Mat (Fin d)) (hQ : Q.IsHermitian) (hQi : Q*Q=Q)
    (k : ℕ) (hk : 0 < k) (hkd : k  ≤  d) (htr : Q.trace=(k : ℂ)) (f : ℝ) (hf : 0 < f) :
    ∃ C : SupportConverter β (⟨0,by simp⟩ : Hamiltonian (Fin d)) (-Real.log ((d : ℝ)/k)/β),
      ∃ p : ℝ, 1-f  ≤  p ∧ p  ≤  1 ∧
        partialRight (partialRight ((
          ((1 : Mat (Fin d)) ⊗ₖ (pureMatrix (fun j : Fin 2 => if j=1 then 1 else 0) ⊗ₖ
            (1 : Mat (Fin C.r)))) ⊗ₖ (1 : Mat (Fin 1))) *
          C.run 1 ((((d : ℂ)⁻¹) • (1 : Mat (Fin d))) ⊗ₖ (1 : Mat (Fin 1))))) =
            (((p/(k : ℝ) : ℝ) : ℂ) • Q) := by
  obtain ⟨L,hlo,hhi⟩ := success_budget f hf
  obtain ⟨D,hD⟩ := square_ladder β hβ d k L hd hk hkd
  obtain ⟨V,hV,hQv⟩ := projection_coordinates d k Q hQ hQi hkd htr
  obtain ⟨C,hC⟩ := rotate_converter β (-gap β d k) (D.converter hk) V hV
  have result : ∃ C : SupportConverter β (zeroHamiltonian d) (-gap β d k),
      ∃ p : ℝ, 1-f ≤ p ∧ p ≤ 1 ∧ flatOutput C=(((p/k : ℝ) : ℂ) • Q) := by
    refine ⟨C,successRate L,hlo,hhi,?_⟩
    rw [hC,hD]
    change V * (_ • rankProjection d k) * Vᴴ = _
    rw [Matrix.mul_smul,Matrix.smul_mul]
    change _ • evolve V (rankProjection d k) = _
    rw [hQv]
  dsimp only [gap] at result
  rw [← neg_div] at result
  exact result

end ScheduleLaw.Blueprint.FiniteFlat

