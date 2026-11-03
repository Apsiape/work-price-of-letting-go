import CacheFactoryExact
import CacheAssemblyTolerances
import CacheDefectBounds
import CacheHardwareReturn

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped Classical BigOperators Kronecker ComplexOrder Topology
namespace ScheduleLaw.Blueprint.CacheProtocol
open History

theorem realizes {I : Inventory} {S : Schedule I} (β : ℝ) (hβ : 0 < β)
    (e : Extension S) (g η : ℝ) (hη : 0 < η) (P : InitializedPlan β e g η) :
    ∃ (p : Driven S β) (b : Budget), Driven.CapitalCharged p ∧
      Approximates p.extension P.bare η ∧ Driven.Meets p b ∧ SmallBudget b η ∧
      (∀ r (t : Tester S r), |Driven.defect p t| ≤ P.residual+η) ∧
      Driven.nominalDebit p ≤ sourceFreeTerm β P.bare P.reference+P.w+η := by
  obtain ⟨C⟩ := small_residue_source_coding P.bare.source
  obtain ⟨a,err,A,hA,ha,herr,herr0,hfamily⟩ :=
    CacheFactoryExact.family P.bare.b_pos β hβ P.bare.source P.reference P.faithful C
  obtain ⟨M,hM,hMexp⟩ := CacheAssemblyTolerances.entropy_cutoff η hη
  obtain ⟨f,hf,hAf⟩ := CacheAssemblyTolerances.factory_failure A η hA hη
  have hnums := CacheAssemblyTolerances.eventually_all P.bare.b a err
    (sourceFreeTerm β P.bare P.reference) A (SourceFunctional.bound β S P.reference)
    (CacheControllerEnergy.spectralSize β P.reference) M η hη ha herr
  obtain ⟨m,hmfamily,hmnums⟩ := (hfamily.and hnums).exists
  obtain ⟨hm,hreturn,hMent,hservice,hAerr,hSent,hEent,hrate⟩ := hmnums
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m≠0)
  obtain ⟨F,bF,hdebit,hacc,hmeets,hprod,hCE,hCS,hBE,hfail,htail,hdef,hcapital,hw,hzero,hexact⟩ :=
    hmfamily 1 f (by norm_num) hf
  simp only [Nat.cast_succ] at hreturn hMent hservice htail hdef
  let p := CacheHardware.hardware P.bare P.reference F P.w
  let b : Budget := ⟨η,η,η,η,η,η⟩
  have hβ0 : β≠0 := hβ.ne'
  have hpos : 0<(n+1 : ℝ) := by positivity
  have hi : 0≤(n+1 : ℝ)⁻¹ := by positivity
  have hinv : (n+1 : ℝ)⁻¹ ≤ η := by
    have hh : (n+1 : ℝ)⁻¹ ≤ 2/(n+1 : ℝ) := by
      rw [div_eq_mul_inv]; nlinarith
    exact hh.trans hreturn
  refine ⟨p,b,CacheHardware.capital_charged _ _ _ _,?_,?_,?_,?_,?_⟩
  · intro z t
    exact (CacheHardwareHistory.service P.bare P.reference F hβ0 P.faithful z t).trans hinv
  · refine ⟨⟨hη.le,hη.le,hη.le,hη.le,hη.le,hη.le⟩,?_⟩
    intro z t
    refine ⟨(CacheHardwareReturn.whole_rest P.bare P.reference F P.w hβ0 P.faithful t).trans hreturn,?_,?_,?_,?_,?_⟩
    · have hh := CacheControllerEnergy.energy_refund P.bare P.reference F P.w hβ0 P.faithful
        (hexact 1 (idleTester F.schedule)) t (err (n+1)) (herr0 _) hacc
      rw [hdebit] at hh
      exact hh.trans hEent
    · exact (CacheControllerRefund.entropy_refund P.bare P.reference F P.w hβ0 P.faithful
        (hexact 1 (idleTester F.schedule)) t (err (n+1)) (herr0 _) hacc).trans hSent
    · have hh := CacheBatteryBudget.entropy_bound P.bare P.reference F P.w hβ0 P.faithful t M
      rw [hw] at hh
      change entropy (Driven.batteryFinal p t) ≤ η
      have hMent' : M*(n+1 : ℝ)⁻¹ ≤ η/2 := by simpa only [div_eq_mul_inv] using hMent
      norm_num only [Nat.cast_ofNat] at hh
      linarith
    · exact (CacheBatteryBudget.failure P.bare P.reference F P.w hβ0 P.faithful t).le.trans hinv
    · change Driven.batteryAbsoluteTail p t ≤ η
      rw [CacheBatteryBudget.absolute_tail P.bare P.reference F P.w hβ0 P.faithful t]
      have hh := mul_le_mul_of_nonneg_left
        (((hmeets.2 _ (idleTester F.schedule)).2.2.2.2.2).trans htail) hi
      have he : (n+1 : ℝ)⁻¹*((n+1 : ℝ)*A*f)=A*f := by
        calc _ = ((n+1 : ℝ)⁻¹*(n+1 : ℝ))*(A*f) := by ring
             _ = A*f := by rw [inv_mul_cancel₀ hpos.ne',one_mul]
      rw [he] at hh
      exact hh.trans (hAf.trans (by linarith))
  · exact ⟨le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl⟩
  · intro z t
    have hh := CacheDefectBounds.defect_bound P.bare P.reference F P.w hβ0 P.faithful t
      P.residual (A*(err (n+1)+f)) (P.initialized z t)
      (by simpa only [mul_assoc] using hdef 1 (idleTester F.schedule))
    have hs : 2*((n+1 : ℝ)⁻¹)*SourceFunctional.bound β S P.reference ≤ η/3 := by
      simpa only [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hservice
    change |Driven.defect p t| ≤ P.residual+η
    nlinarith
  · change Driven.nominalDebit (CacheHardware.hardware P.bare P.reference F P.w) ≤ _
    rw [CacheHardware.nominal_debit,hdebit]
    linarith

end ScheduleLaw.Blueprint.CacheProtocol
