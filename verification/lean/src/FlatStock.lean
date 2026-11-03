import Recorder

/-! Explicit flat preparation of the full counted recorder stock. -/
set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw
namespace Recorder

def flatSource {I : Inventory} (S : Schedule I) : Density (Fin (Fintype.card (Stock S))) where
  matrix := diagonal (fun _ => ((Fintype.card (Stock S) : ℝ)⁻¹ : ℂ))
  positive := by
    have he := epr_reduction (a := Fin (Fintype.card (Stock S)))
    simp only [Fintype.card_fin] at he
    rw [← he]
    exact partialRight_positive (pureMatrix_positive _)
  normalized := by
    letI : Nonempty (Fin (Fintype.card (Stock S))) := ⟨⟨0,Fintype.card_pos⟩⟩
    have he := epr_reduction (a := Fin (Fintype.card (Stock S)))
    simp only [Fintype.card_fin] at he
    rw [← he,partialRight_trace,pureMatrix_trace,epr_normalized,Complex.ofReal_one]

/-- A preparation with the same retained stock space as the recorder. Its
maximally entangled purifier is inert and all its own contacts are identities. -/
def flatStock {I : Inventory} (S : Schedule I) : Extension S where
  b := Fintype.card (Stock S)
  b_pos := Fintype.card_pos
  source := flatSource S
  f := Fintype.card (Stock S)
  f_pos := Fintype.card_pos
  purification := epr
  purification_norm := by
    letI : Nonempty (Fin (Fintype.card (Stock S))) :=
      ⟨⟨0,Fintype.card_pos⟩⟩
    exact epr_normalized
  purification_reduces := by
    simpa only [flatSource,Fintype.card_fin] using
      epr_reduction (a := Fin (Fintype.card (Stock S)))
  gate := fun _ => 1
  unitary := fun _ => by constructor <;> simp
  gate_local := fun k => by
    simpa only [permMatrix_refl] using local_permutation I (Fintype.card (Stock S))
      (held S k) (Equiv.refl _) (Equiv.refl _) (fun _ => rfl)

theorem flatStock_exact {I : Inventory} (S : Schedule I) :
    (flatStock S).source.matrix = diagonal
      (fun _ => ((Fintype.card (Stock S) : ℝ)⁻¹ : ℂ)) := rfl

end Recorder
end ScheduleLaw
