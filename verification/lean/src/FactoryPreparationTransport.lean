import FactoryPreparationBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryPreparationTransport
open History

variable {b : Type} [Fintype b] [DecidableEq b] {d : ℕ}

def density (e : b ≃ Fin d) (ρ : Density b) : Density (Fin d) :=
  ⟨ρ.matrix.submatrix e.symm e.symm,ρ.positive.submatrix _,by
    rw [submatrix_trace_equiv,ρ.normalized]⟩

def frame (e : b ≃ Fin d) (r : ℕ) : b × (Fin 2 × Fin r) ≃ Fin d × (Fin 2 × Fin r) :=
  Equiv.prodCongr e (Equiv.refl _)

def gate {β x : ℝ} {H : Hamiltonian (Fin d)} (e : b ≃ Fin d) (C : SupportConverter β H x) :
    Mat (b × (Fin 2 × Fin C.r)) := C.U.submatrix (frame e C.r) (frame e C.r)

theorem unitary {β x : ℝ} {H : Hamiltonian (Fin d)} (e : b ≃ Fin d)
    (C : SupportConverter β H x) : IsUnitary (gate e C) := unitary_submatrix _ C.unitary

theorem output {β x : ℝ} {H : Hamiltonian (Fin d)} (e : b ≃ Fin d)
    (C : SupportConverter β H x) (ρ : Density b) :
    evolve (gate e C) (ρ.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR))=
      (FactoryFlatRun.state C (density e ρ)).matrix.submatrix (frame e C.r) (frame e C.r) := by
  have hs : ρ.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR)=
      ((density e ρ).matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR)).submatrix
        (frame e C.r) (frame e C.r) := by
    ext ⟨i,w,u⟩ ⟨j,v,z⟩
    simp only [density,frame,submatrix_apply,kroneckerMap_apply,Equiv.prodCongr_apply,
      Prod.map_apply,Equiv.refl_apply,Equiv.symm_apply_apply]
  rw [gate,hs,evolve_submatrix_equiv]
  rfl

theorem work_probability {β x : ℝ} {H : Hamiltonian (Fin d)} (e : b ≃ Fin d)
    (C : SupportConverter β H x) (ρ : Density b) :
    energy ((1 : Mat b) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r))))
      (evolve (gate e C) (ρ.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR)))=
      energy ((1 : Mat (Fin d)) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r))))
        (FactoryFlatRun.state C (density e ρ)).matrix := by
  have he : (1 : Mat b) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r)))=
      (((1 : Mat (Fin d)) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r))))).submatrix
        (frame e C.r) (frame e C.r) := by
    ext ⟨i,w,u⟩ ⟨j,v,z⟩
    simp only [frame,submatrix_apply,kroneckerMap_apply,Equiv.prodCongr_apply,
      Prod.map_apply,Equiv.refl_apply,one_apply,e.injective.eq_iff]
  rw [he,output,energy_reindex]

theorem support_probability {β x : ℝ} {H : Hamiltonian (Fin d)} (e : b ≃ Fin d)
    (C : SupportConverter β H x) (ρ : Density b) (P : Mat (Fin d)) :
    energy (P.submatrix e e) (partialRight
      (evolve (gate e C) (ρ.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR))))=
      energy P (partialRight (FactoryFlatRun.state C (density e ρ)).matrix) := by
  rw [← energy_kron_one,← energy_kron_one P,output]
  have he : P.submatrix e e ⊗ₖ (1 : Mat (Fin 2 × Fin C.r))=
      (P ⊗ₖ (1 : Mat (Fin 2 × Fin C.r))).submatrix (frame e C.r) (frame e C.r) := by
    ext ⟨i,w,u⟩ ⟨j,v,z⟩
    simp only [frame,submatrix_apply,kroneckerMap_apply,Equiv.prodCongr_apply,
      Prod.map_apply,Equiv.refl_apply]
  rw [he,energy_reindex]

/-- The constructed preparation acts on the literal tensor-power batch type,
with both physical probability conclusions transported exactly. -/
theorem prepare (e : b ≃ Fin d) (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (H : Hamiltonian (Fin d)) (U : Mat (Fin d)) (hU : IsUnitary U) (E : Fin d → ℝ)
    (hH : H.matrix=evolve U (diagonal (fun j => (E j : ℂ))))
    (i : Fin d) (f : ℝ) (hf : 0 < f) :
    ∃ C : SupportConverter β H (-E i-Real.log (partition β H)/β-1),
      ∀ ρ : Density b,
        1-f ≤ energy ((1 : Mat b) ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r))))
          (evolve (gate e C) (ρ.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR))) ∧
        1-f ≤ energy ((FactorySupport.eigenProjection U i).submatrix e e) (partialRight
          (evolve (gate e C) (ρ.matrix ⊗ₖ (SupportRun.level 0 ⊗ₖ gibbs β C.HR)))) := by
  obtain ⟨C,hC⟩ := FactoryPreparationBounds.prepare_complete hd β hβ H U hU E hH i f hf
  refine ⟨C,fun ρ => ?_⟩
  rw [work_probability,support_probability]
  exact hC (density e ρ)

end ScheduleLaw.Blueprint.FactoryPreparationTransport
