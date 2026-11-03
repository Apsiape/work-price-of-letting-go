import CacheWorkState
import FactoryDrivenBudgets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheBatteryBudget
open History CacheHardware CacheWorkState FactoryRegisterOutput
variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

theorem marginal_sub {a b c : Type} [Fintype c] (e : a ≃ b × c) (M N : Mat a) :
    marginal e (M-N)=marginal e M-marginal e N := by
  ext i j
  simp only [marginal,partialRight,submatrix_apply,Matrix.sub_apply,Finset.sum_sub_distrib]

theorem difference (F : Formation β τ q (n+1)) (hβ : β≠0) (hq : q.matrix.PosDef) :
    marginal (CacheWorkState.frame F) (CacheMixture.output F)-CacheFlaggedCircuit.level (CacheWorkLedger.nominal F) =
      ((n+1 : ℝ)⁻¹) • (flagged F 1 1 (Driven.batteryFinal F.hardware (idleTester F.schedule))-
        CacheFlaggedCircuit.level (CacheWorkLedger.nominal F)) := by
  have h := congrArg (marginal (CacheWorkState.frame F)) (CacheRareBranch.difference F)
  simpa only [marginal_sub,marginal_smul,ideal_work F,boundary_work F hβ hq,ideal_sector_work F 0] using h

theorem tail_of_difference (F : Formation β τ q (n+1)) (service : ℝ)
    (R : Mat (W F)) (B : Mat (Fin F.hardware.w)) (p : ℝ)
    (h : R-CacheFlaggedCircuit.level (CacheWorkLedger.nominal F)=
      p • (flagged F 1 1 B-CacheFlaggedCircuit.level (CacheWorkLedger.nominal F))) :
    (∑ j,|CacheWorkLedger.energy F service j-CacheWorkLedger.energy F service (CacheWorkLedger.nominal F)| *(R j j).re) =
      p*(∑ j,|F.hardware.batteryEnergy j-F.hardware.batteryEnergy F.hardware.nominalLevel| *(B j j).re) := by
  let E (j : W F) := |CacheWorkLedger.energy F service j-CacheWorkLedger.energy F service (CacheWorkLedger.nominal F)|
  have hzero (j : W F) : E j*(CacheFlaggedCircuit.level (CacheWorkLedger.nominal F) j j).re=0 := by
    by_cases hj : j=CacheWorkLedger.nominal F
    · simp only [E,hj,sub_self,abs_zero,zero_mul]
    · simp [CacheFlaggedCircuit.level,pureMatrix,hj]
  have hp (j : W F) : E j*(R j j).re=p*(E j*(flagged F 1 1 B j j).re) := by
    have hd := congrArg Complex.re (congrFun (congrFun h j) j)
    simp only [Matrix.sub_apply,Matrix.smul_apply,Complex.real_smul,Complex.sub_re,Complex.re_ofReal_mul] at hd
    calc _ = E j*((R j j).re-(CacheFlaggedCircuit.level (CacheWorkLedger.nominal F) j j).re)+
        E j*(CacheFlaggedCircuit.level (CacheWorkLedger.nominal F) j j).re := by ring
         _ = E j*(p*((flagged F 1 1 B j j).re-
           (CacheFlaggedCircuit.level (CacheWorkLedger.nominal F) j j).re)) := by rw [hd,hzero,add_zero]
         _ = p*(E j*(flagged F 1 1 B j j).re)-p*(E j*(CacheFlaggedCircuit.level (CacheWorkLedger.nominal F) j j).re) := by ring
         _ = _ := by rw [hzero]; ring
  change (∑ j,E j*(R j j).re)=_
  simp_rw [hp]
  rw [← Finset.mul_sum]
  congr 1
  simp [E,flagged,submatrix_apply,Equiv.prodAssoc_symm_apply,kroneckerMap_apply,
    Fintype.sum_prod_type,CacheFlaggedCircuit.level,pureMatrix,Fin.sum_univ_two,
    CacheWorkLedger.boundary_tail]

theorem work_card (F : Formation β τ q (n+1)) : w F=4*F.hardware.w := by
  simp only [CacheHardware.w,CacheHardware.W,CacheWorkLedger.Work,Fintype.card_prod,Fintype.card_fin]
  omega

variable {I : Inventory} {S : Schedule I}
variable (bare : Extension S) (ref : Density (Fin bare.b))
    (F : Formation β bare.source ref (n+1)) (service : ℝ)

theorem failure (hβ : β≠0) (hq : ref.matrix.PosDef) {z : ℕ} (t : Tester S z) :
    1-(Driven.batteryFinal (hardware bare ref F service) t
      (nominal F) (nominal F)).re=(n+1 : ℝ)⁻¹ := by
  have he := congrFun (congrFun (difference F hβ hq)
    (CacheWorkLedger.nominal F)) (CacheWorkLedger.nominal F)
  simp only [Matrix.sub_apply,Matrix.smul_apply] at he
  have hn : CacheFlaggedCircuit.level (CacheWorkLedger.nominal F)
      (CacheWorkLedger.nominal F) (CacheWorkLedger.nominal F)=1 := by
    simp [CacheFlaggedCircuit.level,pureMatrix]
  have hb : flagged F 1 1 (Driven.batteryFinal F.hardware (idleTester F.schedule))
      (CacheWorkLedger.nominal F) (CacheWorkLedger.nominal F)=0 := by
    simp [flagged,CacheFlaggedCircuit.level,pureMatrix,CacheWorkLedger.nominal]
  rw [hn,hb] at he
  have hd := congrArg Complex.re he
  have hs : (((n+1 : ℝ)⁻¹) • (0-1 : ℂ)).re= -(n+1 : ℝ)⁻¹ := by
    rw [Complex.real_smul,Complex.re_ofReal_mul]
    norm_num
  rw [hs] at hd
  simp only [Complex.sub_re,Complex.one_re] at hd
  rw [CacheWorkState.output bare ref F service hβ hq t]
  change 1-((marginal (CacheWorkState.frame F) (CacheMixture.output F))
    ((Fintype.equivFin (W F)).symm (nominal F))
    ((Fintype.equivFin (W F)).symm (nominal F))).re=_
  simp only [nominal,Equiv.symm_apply_apply]
  linarith

theorem absolute_tail (hβ : β≠0) (hq : ref.matrix.PosDef) {z : ℕ} (t : Tester S z) :
    Driven.batteryAbsoluteTail (hardware bare ref F service) t =
      (n+1 : ℝ)⁻¹*Driven.batteryAbsoluteTail F.hardware (idleTester F.schedule) := by
  change (∑ j : Fin (w F),|workEnergy F service j-workEnergy F service (nominal F)| *
    (Driven.batteryFinal (hardware bare ref F service) t j j).re)=_
  rw [CacheWorkState.output bare ref F service hβ hq t]
  conv_lhs => rw [← Equiv.sum_comp (Fintype.equivFin (W F))]
  simp only [battery,workEnergy,nominal,submatrix_apply,Equiv.symm_apply_apply]
  exact tail_of_difference F service _ _ _ (difference F hβ hq)

theorem entropy_bound (hβ : β≠0) (hq : ref.matrix.PosDef) {z : ℕ} (t : Tester S z) (M : ℝ) :
    entropy (Driven.batteryFinal (hardware bare ref F service) t) ≤
      M*(n+1 : ℝ)⁻¹+(4*F.hardware.w : ℝ)*Real.exp (-M) := by
  have h := FactoryBattery.entropy_bound
    (FactoryDrivenBudgets.batteryDensity (hardware bare ref F service) t) (nominal F) M
  simp only [Fintype.card_fin] at h
  change entropy (Driven.batteryFinal (hardware bare ref F service) t) ≤
    M*(1-(Driven.batteryFinal (hardware bare ref F service) t (nominal F) (nominal F)).re)+
      (w F : ℝ)*Real.exp (-M) at h
  rw [failure bare ref F service hβ hq t,work_card F] at h
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using h

end ScheduleLaw.Blueprint.CacheBatteryBudget
