import CacheRareBranch

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheRareProduct
open History

variable {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem kron_sub (C : Mat a) (X Y : Mat b) : C ⊗ₖ (X-Y)=C ⊗ₖ X-C ⊗ₖ Y := by
  ext i j; simp only [kroneckerMap_apply,Matrix.sub_apply,mul_sub]

theorem sub_kron (X Y : Mat a) (C : Mat b) : (X-Y) ⊗ₖ C=X ⊗ₖ C-Y ⊗ₖ C := by
  ext i j; simp only [kroneckerMap_apply,Matrix.sub_apply,sub_mul]

theorem distance_of_difference (X Y : Mat a) (A B : Density a) (p : ℝ) (hp : 0≤p)
    (h : X-Y=p • (A.matrix-B.matrix)) : traceDistance X Y ≤ p := by
  have he : p • (A.matrix-B.matrix)=(p : ℂ) • (A.matrix-B.matrix) := by
    ext i j
    simp only [smul_apply,Complex.real_smul,smul_eq_mul]
  have hd := ClassicalFlag.density_distance_le_one A B
  unfold traceDistance at *
  rw [h,he,ClassicalFlag.traceNorm_eq_library,Matrix.traceNorm_smul]
  simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hp]
  rw [ClassicalFlag.traceNorm_eq_library] at hd
  nlinarith [mul_le_mul_of_nonneg_left hd hp]

def rightDensity (ρ : Density (a × b)) : Density b :=
  ⟨partialLeft ρ.matrix,partialLeft_positive ρ.positive,(partialLeft_trace _).trans ρ.normalized⟩

def tensorDensity (ρ : Density a) (σ : Density b) : Density (a × b) :=
  ⟨ρ.matrix ⊗ₖ σ.matrix,ρ.positive.kronecker σ.positive,by
    rw [trace_kronecker,ρ.normalized,σ.normalized,one_mul]⟩

/-- A rare full-state replacement controls the complete controller/rest
product defect. No independence of either rare branch is assumed. -/
theorem whole_rest (ρC : Density a) (σ : Density b) (ρ : Mat (a × b))
    (A B : Density (a × b)) (p : ℝ) (hp : 0≤p)
    (h : ρ-ρC.matrix ⊗ₖ σ.matrix=p • (A.matrix-B.matrix)) :
    traceDistance ρ (ρC.matrix ⊗ₖ partialLeft ρ) ≤ 2*p := by
  have h1 := distance_of_difference ρ (ρC.matrix ⊗ₖ σ.matrix) A B p hp h
  have hm : partialLeft ρ-σ.matrix=p • (partialLeft A.matrix-partialLeft B.matrix) := by
    have hs (X Y : Mat (a × b)) : partialLeft (X-Y)=partialLeft X-partialLeft Y := by
      ext i j; simp [partialLeft,Finset.sum_sub_distrib]
    have ht (X : Mat (a × b)) : partialLeft (p • X)=p • partialLeft X := by
      ext i j; simp [partialLeft,Finset.smul_sum]
    have hh := congrArg partialLeft h
    simpa only [hs,ht,partialLeft_kron,ρC.normalized,one_smul] using hh
  let U := tensorDensity ρC (rightDensity B)
  let V := tensorDensity ρC (rightDensity A)
  have ht : ρC.matrix ⊗ₖ σ.matrix-ρC.matrix ⊗ₖ partialLeft ρ=p • (U.matrix-V.matrix) := by
    have hh := congrArg (fun M => ρC.matrix ⊗ₖ M) hm
    simp only [kron_sub,kronecker_smul] at hh
    dsimp only [U,V,tensorDensity,rightDensity]
    calc _ = -(ρC.matrix ⊗ₖ partialLeft ρ-ρC.matrix ⊗ₖ σ.matrix) := by abel
         _ = -(p • (ρC.matrix ⊗ₖ partialLeft A.matrix-ρC.matrix ⊗ₖ partialLeft B.matrix)) := by rw [hh]
         _ = _ := by rw [← smul_neg]; congr 1; abel
  have h2 := distance_of_difference (ρC.matrix ⊗ₖ σ.matrix)
    (ρC.matrix ⊗ₖ partialLeft ρ) U V p hp ht
  exact (FactoryOutput.distance_triangle ρ (ρC.matrix ⊗ₖ σ.matrix)
    (ρC.matrix ⊗ₖ partialLeft ρ)).trans (by linarith)

end ScheduleLaw.Blueprint.CacheRareProduct
