import BlueprintFinitePrimitives
import FactoryGibbs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactorySupport
open History

def eigenProjection {d : ℕ} (U : Mat (Fin d)) (i : Fin d) : Mat (Fin d) :=
  evolve U (diagonal (fun j => if j=i then 1 else 0))

theorem prepare_eigenvector {d : ℕ} (hd : 0<d) (β : ℝ) (hβ : 0<β)
    (H : Hamiltonian (Fin d)) (U : Mat (Fin d)) (hU : IsUnitary U) (E : Fin d → ℝ)
    (hH : H.matrix=evolve U (diagonal (fun j => (E j : ℂ))))
    (i : Fin d) (f : ℝ) (hf : 0<f) :
    ∃ C : SupportConverter β H (-E i-Real.log (partition β H)/β-1),
      ∀ z (ρ : Density (Fin d × Fin z)),
      1-f ≤ energy ((eigenProjection U i ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r)))) ⊗ₖ
        (1 : Mat (Fin z))) (C.run z ρ.matrix) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  let D : Mat (Fin d) := diagonal (fun j => if j=i then 1 else 0)
  let Q := eigenProjection U i
  let A : Mat (Fin d) := diagonal (fun j => (E j : ℂ))
  let φ := Unitary.conjStarAlgAut ℂ (Mat (Fin d)) (⟨U,hU⟩ : unitaryGroup (Fin d) ℂ)
  have hDi : D*D=D := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext j
    split_ifs <;> norm_num
  have hD : D.IsHermitian := by
    rw [isHermitian_diagonal_iff]
    intro j
    split_ifs <;> simp
  have hQ : Q.IsHermitian := Matrix.isHermitian_mul_mul_conjTranspose U hD
  have hQi : Q*Q=Q := by
    change φ D*φ D=φ D
    rw [← map_mul,hDi]
  have hQH : Q*H.matrix=H.matrix*Q := by
    have hφ : φ A=H.matrix := hH.symm
    change φ D*H.matrix=H.matrix*φ D
    rw [← hφ,← map_mul,← map_mul]
    congr 1
    simp only [D,A,diagonal_mul_diagonal,mul_comm]
  have hZQ : energy Q (boltzmann β H)=Real.exp (-β*E i) := by
    rw [SupportBasis.boltzmann_in_basis β H U hU E hH]
    change ((φ D*φ (diagonal (fun j => (Real.exp (-β*E j) : ℂ)))).trace).re = _
    rw [← map_mul]
    change (evolve U (D*diagonal (fun j => (Real.exp (-β*E j) : ℂ)))).trace.re = _
    rw [evolve,trace_mul_cycle,hU.1,one_mul]
    simp [D,diagonal_mul_diagonal,trace_diagonal,ite_mul]
    rw [← Complex.ofReal_mul,← Complex.ofReal_neg,← Complex.ofReal_exp]
    rfl
  have hZP : energy (1 : Mat (Fin d)) (boltzmann β H)=partition β H := by
    unfold energy boltzmann Matrix.IsHermitian.cfc
    rw [one_mul,trace_unitary_conjugation]
    simp only [trace_diagonal,Complex.re_sum,Function.comp_apply]
    rfl
  have hpart := partition_positive β H
  have hx : -E i-Real.log (partition β H)/β-1 <
      Real.log (energy Q (boltzmann β H)/energy (1 : Mat (Fin d)) (boltzmann β H))/β := by
    rw [hZP,hZQ,Real.log_div (Real.exp_ne_zero _) hpart.ne',Real.log_exp]
    have he : (-β*E i-Real.log (partition β H))/β = -E i-Real.log (partition β H)/β := by
      field_simp
    rw [he]
    linarith
  obtain ⟨C,hC⟩ := energy_shell_support_conversion hd β hβ H 1 Q (by simp [Matrix.IsHermitian])
    (by simp) hQ hQi (by simp) hQH (by rw [hZP]; exact hpart)
    (by rw [hZQ]; exact Real.exp_pos _) _ f hx hf
  refine ⟨C,fun z ρ => ?_⟩
  exact hC z ρ (by rw [one_kronecker_one,one_mul])

end ScheduleLaw.Blueprint.FactorySupport
