import CacheHardware
import FactoryResetCircuit

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheTerminalReset
open History

variable {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq a] [DecidableEq b] [DecidableEq c]

def hamiltonian (H : Mat a) (K : Mat b) : Mat (a × (b × a)) :=
  H ⊗ₖ (1 : Mat (b × a))+
    (1 : Mat a) ⊗ₖ (K ⊗ₖ (1 : Mat a)+(1 : Mat b) ⊗ₖ H)

/-- The terminal q swap conserves its actual nonzero tangent Hamiltonian,
while retaining an arbitrary Hamiltonian and correlations on the whole rest. -/
theorem conserving (H : Mat a) (K : Mat b) :
    Conserves ((FactoryReset.swap (a:=a) (b:=b)).permMatrix ℂ) (hamiltonian H K) := by
  have hs : ((FactoryReset.swap (a:=a) (b:=b)).permMatrix ℂ)ᴴ=
      (FactoryReset.swap (a:=a) (b:=b)).permMatrix ℂ := by
    rw [conjTranspose_permMatrix]
    rfl
  have he := Recorder.permutation_evolve (FactoryReset.swap (a:=a) (b:=b)) (hamiltonian H K)
  rw [evolve,hs] at he
  unfold Conserves
  rw [hs,he]
  ext ⟨i,r,k⟩ ⟨j,s,l⟩
  simp only [hamiltonian,submatrix_apply,FactoryReset.swap,Equiv.coe_fn_mk,
    kroneckerMap_apply,Matrix.add_apply,Matrix.one_apply,Prod.mk.injEq]
  by_cases hij : i=j <;> by_cases hrs : r=s <;> by_cases hkl : k=l <;>
    simp [hij,hrs,hkl] <;> ring

theorem reindexed_conserving (e : c ≃ a × (b × a)) (H : Mat a) (K : Mat b) :
    Conserves (((FactoryReset.swap (a:=a) (b:=b)).permMatrix ℂ).submatrix e e)
      ((hamiltonian H K).submatrix e e) :=
  conserves_reindex e _ _ (conserving H K)

/-- No output/residue factorization is required before the reset. The
entire old joint state becomes retained rest and the fresh stock is exact. -/
theorem output (ρ : Mat (a × b)) (q : Mat a) :
    evolve ((FactoryReset.swap (a:=a) (b:=b)).permMatrix ℂ)
      ((ρ ⊗ₖ q).submatrix (Equiv.prodAssoc a b a).symm (Equiv.prodAssoc a b a).symm) =
      q ⊗ₖ (ρ.submatrix (Equiv.prodComm b a) (Equiv.prodComm b a)) :=
  FactoryReset.whole_rest_return ρ q

end ScheduleLaw.Blueprint.CacheTerminalReset
