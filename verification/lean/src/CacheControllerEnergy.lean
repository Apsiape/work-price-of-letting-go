import CacheControllerRefund

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.CacheControllerEnergy
open History CacheHardware
variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

def cacheH (F : Formation β τ q (n+1)) : Hamiltonian (Fin (n+1) × (Fin n → Fin d)) :=
  FactoryGibbs.sumHamiltonian
    (FlatMatrix.diagonalHamiltonian (Fin (n+1)) (CacheClockAdvance.clockEnergy n F.debit))
    (FactoryTensor.hamiltonian (FactoryGibbs.tangent β q) n)

def spectralSize (β : ℝ) (q : Density (Fin d)) : ℝ :=
  ∑ i,|(FactoryGibbs.tangent β q).hermitian.eigenvalues i|

theorem spectral_nonneg : 0 ≤ spectralSize β q := Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem norm_bound (F : Formation β τ q (n+1)) :
    ‖(cacheH F).matrix‖ ≤ (n+1 : ℝ)*(|F.debit|+spectralSize β q) := by
  let H := FactoryGibbs.tangent β q
  let U : Mat (Fin d) := H.hermitian.eigenvectorUnitary
  let E := H.hermitian.eigenvalues
  let V := FiniteResidue.tensorMatrix U n
  have hu : IsUnitary U := H.hermitian.eigenvectorUnitary.property
  have hv : IsUnitary V := FiniteResidue.tensorMatrix_unitary U hu n
  have hi : IsUnitary (1 : Mat (Fin (n+1))) := by constructor <;> simp
  have hc : (FlatMatrix.diagonalHamiltonian (Fin (n+1)) (CacheClockAdvance.clockEnergy n F.debit)).matrix=
      evolve (1 : Mat (Fin (n+1))) (diagonal (fun k => (CacheClockAdvance.clockEnergy n F.debit k : ℂ))) := by
    simp [FlatMatrix.diagonalHamiltonian,evolve]
  have ht : (FactoryTensor.hamiltonian H n).matrix=evolve V
      (diagonal (fun u : Fin n → Fin d => ((∑ j,E (u j) : ℝ) : ℂ))) :=
    FactoryTensor.tensorHamiltonian_in_basis H.matrix U hu E H.hermitian.spectral_theorem n
  have he := FactoryGibbs.sum_in_basis
    (FlatMatrix.diagonalHamiltonian (Fin (n+1)) (CacheClockAdvance.clockEnergy n F.debit))
    (FactoryTensor.hamiltonian H n) (1 : Mat (Fin (n+1))) V hi hv
    (CacheClockAdvance.clockEnergy n F.debit) (fun u : Fin n → Fin d => ∑ j,E (u j)) hc ht
  change ‖(FactoryGibbs.sumHamiltonian _ _).matrix‖ ≤ _
  rw [he,FactoryEnergy.norm_evolve _ _ (unitary_kron hi hv),Matrix.l2_opNorm_diagonal]
  have hΛ := spectral_nonneg (β:=β) (q:=q)
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ (n+1 : ℝ)*(|F.debit|+spectralSize β q))).mpr
  rintro ⟨k,u⟩
  simp only [Complex.norm_real,Real.norm_eq_abs]
  have hclock : |CacheClockAdvance.clockEnergy n F.debit k| ≤ (n : ℝ)*|F.debit| := by
    rw [CacheClockAdvance.clockEnergy,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n k.val) (abs_nonneg _)
  have hsum : |∑ j : Fin n,E (u j)| ≤ (n : ℝ)*spectralSize β q := by
    calc _  ≤  ∑ j : Fin n,|E (u j)| := Finset.abs_sum_le_sum_abs _ _
         _  ≤  ∑ _ : Fin n,spectralSize β q := by
           apply Finset.sum_le_sum
           intro j _
           exact Finset.single_le_sum (fun i _ => abs_nonneg (E i)) (Finset.mem_univ (u j))
         _ = _ := by simp
  exact (abs_add_le _ _).trans ((add_le_add hclock hsum).trans (by
    nlinarith [spectral_nonneg (β:=β) (q:=q),abs_nonneg F.debit]))

variable {I : Inventory} {S : Schedule I}
variable (bare : Extension S) (ref : Density (Fin bare.b))
    (F : Formation β bare.source ref (n+1)) (service : ℝ)

theorem final_matrix (hβ : β≠0) (hq : ref.matrix.PosDef)
    (hexact : ∃ σ : Density ((Fin F.hardware.w × Fin F.hardware.r) × (Payload F.inventory × Fin 1)),
      FactoryControllerReturn.wholeState F.hardware (idleTester F.schedule)=F.hardware.controller.matrix ⊗ₖ σ.matrix)
    {z : ℕ} (t : Tester S z) :
    Driven.controllerFinal (hardware bare ref F service) t=
      ((CacheMarginalAccuracy.cache F).matrix ⊗ₖ F.hardware.controller.matrix).submatrix
        (Fintype.equivFin (C F)).symm (Fintype.equivFin (C F)).symm := by
  have h := congrArg (fun M : Mat (C F) => M.submatrix
    (Fintype.equivFin (C F)).symm (Fintype.equivFin (C F)).symm)
    (CacheControllerRefund.actual_factor bare ref F service hβ hq hexact t)
  simpa only [submatrix_submatrix,Equiv.self_comp_symm,submatrix_id_id] using h

theorem energy_change (hβ : β≠0) (hq : ref.matrix.PosDef)
    (hexact : ∃ σ : Density ((Fin F.hardware.w × Fin F.hardware.r) × (Payload F.inventory × Fin 1)),
      FactoryControllerReturn.wholeState F.hardware (idleTester F.schedule)=F.hardware.controller.matrix ⊗ₖ σ.matrix)
    {z : ℕ} (t : Tester S z) :
    Driven.controllerEnergyChange (hardware bare ref F service) t=
      energy (cacheH F).matrix (CacheMarginalAccuracy.cache F).matrix-
        energy (cacheH F).matrix (CacheControllerReturn.cache bare.source ref n).matrix := by
  change energy (HC F).matrix (Driven.controllerFinal (hardware bare ref F service) t)-
    energy (HC F).matrix (controller F).matrix=_
  rw [final_matrix bare ref F service hβ hq hexact t]
  change energy ((rawHC F).matrix.submatrix (Fintype.equivFin (C F)).symm (Fintype.equivFin (C F)).symm)
      (((CacheMarginalAccuracy.cache F).matrix ⊗ₖ F.hardware.controller.matrix).submatrix _ _)-
    energy ((rawHC F).matrix.submatrix (Fintype.equivFin (C F)).symm (Fintype.equivFin (C F)).symm)
      (((CacheControllerReturn.cache bare.source ref n).matrix ⊗ₖ F.hardware.controller.matrix).submatrix _ _)=_
  rw [energy_reindex,energy_reindex]
  change energy ((cacheH F).matrix ⊗ₖ (1 : Mat (Fin F.hardware.c))+
      (1 : Mat (Fin (n+1) × (Fin n → Fin bare.b))) ⊗ₖ F.hardware.HC.matrix)
      ((CacheMarginalAccuracy.cache F).matrix ⊗ₖ F.hardware.controller.matrix)-
    energy ((cacheH F).matrix ⊗ₖ (1 : Mat (Fin F.hardware.c))+
      (1 : Mat (Fin (n+1) × (Fin n → Fin bare.b))) ⊗ₖ F.hardware.HC.matrix)
      ((CacheControllerReturn.cache bare.source ref n).matrix ⊗ₖ F.hardware.controller.matrix)=_
  rw [energy_add,energy_add,energy_kron_one,energy_one_kron,energy_kron_one,energy_one_kron]
  simp only [partialRight_kron,partialLeft_kron,(CacheMarginalAccuracy.cache F).normalized,
    (CacheControllerReturn.cache bare.source ref n).normalized,F.hardware.controller.normalized,one_smul]
  ring

theorem energy_refund (hβ : β≠0) (hq : ref.matrix.PosDef)
    (hexact : ∃ σ : Density ((Fin F.hardware.w × Fin F.hardware.r) × (Payload F.inventory × Fin 1)),
      FactoryControllerReturn.wholeState F.hardware (idleTester F.schedule)=F.hardware.controller.matrix ⊗ₖ σ.matrix)
    {z : ℕ} (t : Tester S z) (ε : ℝ) (hε : 0 ≤ ε)
    (hacc : traceDistance F.output (tensorPower bare.source.matrix (n+1)) ≤ ε) :
    |Driven.controllerEnergyChange (hardware bare ref F service) t| ≤ 
      2*(|F.debit|+spectralSize β ref)*ε := by
  rw [energy_change bare ref F service hβ hq hexact t]
  apply CacheRefundBounds.energy_refund _ _ _ n (|F.debit|+spectralSize β ref) ε
    (add_nonneg (abs_nonneg _) spectral_nonneg) hε (norm_bound F)
  exact (CacheMarginalAccuracy.accuracy F hβ hq).trans
    (div_le_div_of_nonneg_right hacc (by positivity))

end ScheduleLaw.Blueprint.CacheControllerEnergy
