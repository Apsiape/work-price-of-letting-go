import CachePhysicalDefect
import CacheControllerEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheDefectBounds
open History CacheHardware CacheHardwareHistory
variable {I : Inventory} {S : Schedule I} {n : ℕ} {β : ℝ}

theorem source_difference (bare : Extension S) {N : ℕ} {a : Type} [Fintype a]
    (e : Fin N ≃ Fin bare.b × a) (ρ σ A B : Density (Fin N)) (p : ℝ)
    (h : ρ.matrix-σ.matrix=p • (A.matrix-B.matrix)) :
    (ServiceSourceMarginal.source bare e ρ).matrix-(ServiceSourceMarginal.source bare e σ).matrix=
      p • ((ServiceSourceMarginal.source bare e A).matrix-(ServiceSourceMarginal.source bare e B).matrix) := by
  ext i j
  have hh := congrArg (fun M : Mat (Fin N) => partialRight (M.submatrix e.symm e.symm) i j) h
  simpa only [ServiceSourceMarginal.source,partialRight,submatrix_apply,Matrix.sub_apply,
    Matrix.smul_apply,Finset.sum_sub_distrib,← Finset.smul_sum] using hh

variable (bare : Extension S) (ref : Density (Fin bare.b))
    (F : Formation β bare.source ref (n+1)) (service : ℝ)

theorem ideal_source :
    (ServiceSourceMarginal.source bare ((bodyFrame F).trans (activeFrame F)) (idealSource F)).matrix=bare.source.matrix := by
  change partialRight ((idealSource F).matrix.submatrix
    ((bodyFrame F).trans (activeFrame F)).symm ((bodyFrame F).trans (activeFrame F)).symm)=bare.source.matrix
  rw [ideal_product bare ref F]
  simp only [submatrix_submatrix,Equiv.self_comp_symm,submatrix_id_id,
    partialRight_kron,(idleStock F).normalized,one_smul]

theorem prepared_difference (hβ : β≠0) (hq : ref.matrix.PosDef) :
    (ServiceSourceMarginal.source bare ((bodyFrame F).trans (activeFrame F)) (prepared bare ref F)).matrix-bare.source.matrix=
      ((n+1 : ℝ)⁻¹) •
        ((ServiceSourceMarginal.source bare ((bodyFrame F).trans (activeFrame F)) (actualBoundary F)).matrix-
          (ServiceSourceMarginal.source bare ((bodyFrame F).trans (activeFrame F)) (idealBoundary F)).matrix) := by
  have h := source_difference bare ((bodyFrame F).trans (activeFrame F))
    (prepared bare ref F) (idealSource F) (actualBoundary F) (idealBoundary F) ((n+1 : ℝ)⁻¹)
    (CacheHardwareHistory.difference bare ref F hβ hq)
  rw [ideal_source bare ref F] at h
  exact h

theorem service_error (hβ : β≠0) (hq : ref.matrix.PosDef) {z : ℕ} (t : Tester S z) :
    |physicalLinearized β (CacheSourceHistory.withSource bare
      (ServiceSourceMarginal.source bare ((bodyFrame F).trans (activeFrame F)) (prepared bare ref F))) ref t-
      physicalLinearized β bare ref t| ≤ 2*((n+1 : ℝ)⁻¹)*SourceFunctional.bound β S ref := by
  have h := SourceFunctional.rare_error β bare ref
    (ServiceSourceMarginal.source bare ((bodyFrame F).trans (activeFrame F)) (prepared bare ref F)) bare.source
    (ServiceSourceMarginal.source bare ((bodyFrame F).trans (activeFrame F)) (actualBoundary F))
    (ServiceSourceMarginal.source bare ((bodyFrame F).trans (activeFrame F)) (idealBoundary F))
    ((n+1 : ℝ)⁻¹) (by positivity) (prepared_difference bare ref F hβ hq) t
  rw [ServiceEnergyTelescope.physical_same_source] at h
  exact h

theorem defect_bound (hβ : β≠0) (hq : ref.matrix.PosDef) {z : ℕ} (t : Tester S z)
    (R D : ℝ) (hplan : |physicalLinearized β bare ref t-service| ≤ R)
    (hfactory : |Driven.defect F.hardware (idleTester F.schedule)| ≤ (n+1 : ℝ)*D) :
    |Driven.defect (hardware bare ref F service) t| ≤ R+2*((n+1 : ℝ)⁻¹)*SourceFunctional.bound β S ref+D := by
  have hs := service_error bare ref F hβ hq t
  have hd : |Driven.defect F.hardware (idleTester F.schedule)/(n+1 : ℝ)| ≤ D := by
    rw [abs_div,abs_of_pos (by positivity : 0<(n+1 : ℝ))]
    exact (div_le_iff₀ (by positivity : 0<(n+1 : ℝ))).mpr (by nlinarith [hfactory])
  let J := physicalLinearized β (CacheSourceHistory.withSource bare
    (ServiceSourceMarginal.source bare ((bodyFrame F).trans (activeFrame F)) (prepared bare ref F))) ref t
  let B := physicalLinearized β bare ref t
  calc _ = |(J-B)+(B-service)+Driven.defect F.hardware (idleTester F.schedule)/(n+1 : ℝ)| := by
         rw [CachePhysicalDefect.exact_ledger bare ref F service hβ hq t]
         congr 1
         dsimp only [J,B]
         ring
       _ ≤ |(J-B)+(B-service)|+|Driven.defect F.hardware (idleTester F.schedule)/(n+1 : ℝ)| := abs_add_le _ _
       _ ≤ (2*((n+1 : ℝ)⁻¹)*SourceFunctional.bound β S ref+R)+D :=
         add_le_add ((abs_add_le _ _).trans (add_le_add hs hplan)) hd
       _ = _ := by ring

end ScheduleLaw.Blueprint.CacheDefectBounds
