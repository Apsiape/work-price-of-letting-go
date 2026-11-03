import PhaseLatticeBox
import PhaseVectorDistance
import FactoryGibbs
import IdleExtension

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseGateDilation
open PhaseLatticeBox
variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem adjoint_unitary (U : Mat a) (hU : IsUnitary U) : IsUnitary Uᴴ := by
  constructor
  · simpa only [conjTranspose_conjTranspose] using hU.2
  · simpa only [conjTranspose_conjTranspose] using hU.1

theorem conjugate_unitary (U V : Mat a) (hU : IsUnitary U) (hV : IsUnitary V) :
    IsUnitary (evolve V U) :=
  unitary_mul (unitary_mul hV hU) (adjoint_unitary V hV)

theorem conjugate_conserves (U V H : Mat a) (hV : IsUnitary V) (hU : Conserves U H) :
    Conserves (evolve V U) (evolve V H) := by
  have hm (A B : Mat a) : evolve V A*evolve V B=evolve V (A*B) := by
    unfold evolve
    simp only [mul_assoc]
    rw [← mul_assoc Vᴴ V,hV.1,one_mul]
  have hstar : (evolve V U)ᴴ=evolve V Uᴴ := by
    simp only [evolve,conjTranspose_mul,conjTranspose_conjTranspose,mul_assoc]
  unfold Conserves
  rw [hstar,hm,hm,hU]

theorem diagonal_total (E : a → ℝ) (K : b → ℝ) :
    diagonal (fun x : a × b => ((E x.1+K x.2 : ℝ) : ℂ))=
      diagonal (fun i => (E i : ℂ)) ⊗ₖ (1 : Mat b)+
        (1 : Mat a) ⊗ₖ diagonal (fun j => (K j : ℂ)) := by
  ext ⟨i,k⟩ ⟨j,l⟩
  by_cases hij : i=j <;> by_cases hkl : k=l <;>
    simp [diagonal_apply,Matrix.one_apply,kroneckerMap_apply,Prod.mk.injEq,hij,hkl]

def basis (H : Hamiltonian a) : Mat a := H.hermitian.eigenvectorUnitary

def energies (H : Hamiltonian a) : a → ℝ := H.hermitian.eigenvalues

def phaseH (H : Hamiltonian a) (L : ℕ) : Hamiltonian ↥(box a L) :=
  FlatMatrix.diagonalHamiltonian ↥(box a L) (fun x => frequency (energies H) x.val)

def inBasis (H : Hamiltonian a) (U : Mat a) : Mat a := evolve (basis H)ᴴ U

def gate (H : Hamiltonian a) (U : Mat a) (L : ℕ) : Mat (a × ↥(box a L)) :=
  evolve (basis H ⊗ₖ (1 : Mat ↥(box a L)))
    (FinitePhaseShell.gate label (box a L) (inBasis H U))

theorem basis_unitary (H : Hamiltonian a) : IsUnitary (basis H) :=
  H.hermitian.eigenvectorUnitary.property

theorem unitary (H : Hamiltonian a) (U : Mat a) (hU : IsUnitary U) (L : ℕ) :
    IsUnitary (gate H U L) := by
  apply conjugate_unitary
  · apply FinitePhaseShell.unitary
    exact conjugate_unitary U _ hU (adjoint_unitary _ (basis_unitary H))
  · exact unitary_kron (basis_unitary H) (by constructor <;> simp)

/-- An arbitrary finite unitary has an actual finite full-square conserving
phase dilation for its original, possibly noncommensurate Hamiltonian. -/
theorem conserving (H : Hamiltonian a) (U : Mat a) (hU : IsUnitary U) (L : ℕ) :
    Conserves (gate H U L)
      (H.matrix ⊗ₖ (1 : Mat ↥(box a L))+(1 : Mat a) ⊗ₖ (phaseH H L).matrix) := by
  let W := basis H ⊗ₖ (1 : Mat ↥(box a L))
  let D := diagonal (fun i => (energies H i : ℂ))
  let T := D ⊗ₖ (1 : Mat ↥(box a L))+(1 : Mat a) ⊗ₖ (phaseH H L).matrix
  have hW : IsUnitary W := unitary_kron (basis_unitary H) (by constructor <;> simp)
  have hB : IsUnitary (inBasis H U) :=
    conjugate_unitary U _ hU (adjoint_unitary _ (basis_unitary H))
  have hs := FinitePhaseShell.conserving label (box a L) (frequency (energies H)) (inBasis H U) hB
  simp only [frequency_label] at hs
  rw [diagonal_total (energies H) (fun x : ↥(box a L) => frequency (energies H) x.val)] at hs
  have ht : Conserves (FinitePhaseShell.gate label (box a L) (inBasis H U)) T := hs
  have hh := conjugate_conserves _ W T hW ht
  have he : evolve W T=H.matrix ⊗ₖ (1 : Mat ↥(box a L))+(1 : Mat a) ⊗ₖ (phaseH H L).matrix := by
    change evolve W (D ⊗ₖ (1 : Mat ↥(box a L))+(1 : Mat a) ⊗ₖ (phaseH H L).matrix)=_
    have hadd (A B : Mat (a × ↥(box a L))) : evolve W (A+B)=evolve W A+evolve W B := by
      simp only [evolve,mul_add,add_mul]
    rw [hadd]
    change evolve (basis H ⊗ₖ (1 : Mat ↥(box a L))) (D ⊗ₖ (1 : Mat ↥(box a L)))+
      evolve (basis H ⊗ₖ (1 : Mat ↥(box a L))) ((1 : Mat a) ⊗ₖ (phaseH H L).matrix)=_
    rw [IdleExtension.evolve_idle,IdleExtension.evolve_idle]
    have hD : evolve (basis H) D=H.matrix := H.hermitian.spectral_theorem.symm
    have h1 : evolve (basis H) (1 : Mat a)=1 := by
      simpa only [evolve,mul_one] using (basis_unitary H).2
    rw [hD,h1]
  rw [he] at hh
  exact hh

end ScheduleLaw.Blueprint.PhaseGateDilation
