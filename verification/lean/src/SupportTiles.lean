import FlatGibbs
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped BigOperators
namespace ScheduleLaw.Blueprint.SupportTiles

theorem strict_capacity_margin (β ZP ZQ x : ℝ) (hβ : 0<β)
    (hP : 0<ZP) (hQ : 0<ZQ) (hx : x<Real.log (ZQ/ZP)/β) :
    ∃ θ : ℝ, 0<θ ∧ θ<1 ∧ ZP<(1-θ)*Real.exp (-β*x)*ZQ := by
  have hlog : β*x<Real.log (ZQ/ZP) := by
    have h := (lt_div_iff₀ hβ).mp hx
    nlinarith
  have he : Real.exp (β*x)<ZQ/ZP := by
    simpa only [Real.exp_log (div_pos hQ hP)] using Real.exp_lt_exp.mpr hlog
  have hp : Real.exp (β*x)*ZP<ZQ := (lt_div_iff₀ hP).mp he
  have hi : Real.exp (-β*x)*Real.exp (β*x)=1 := by
    rw [← Real.exp_add,show -β*x+β*x=0 by ring,Real.exp_zero]
  let r := Real.exp (-β*x)*ZQ
  have hr : 0<r := mul_pos (Real.exp_pos _) hQ
  have hPr : ZP<r := by
    calc
      ZP = Real.exp (-β*x)*(Real.exp (β*x)*ZP) := by rw [← mul_assoc,hi,one_mul]
      _ < r := mul_lt_mul_of_pos_left hp (Real.exp_pos _)
  let θ := (r-ZP)/(2*r)
  have hθ : 0<θ := div_pos (sub_pos.mpr hPr) (by positivity)
  have hθ1 : θ<1 := by
    apply (div_lt_iff₀ (by positivity : 0<2*r)).mpr
    nlinarith
  refine ⟨θ,hθ,hθ1,?_⟩
  have ht : θ*(2*r)=r-ZP := div_mul_cancel₀ _ (by positivity)
  have hg : ZP<(1-θ)*r := by nlinarith
  simpa only [r,mul_assoc] using hg

theorem relative_floor (a K θ : ℝ) (ha : 0≤a) (hK : 0≤K)
    (hscale : 1≤θ*K*a) :
    (1-θ)*K*a ≤ (⌊K*a⌋₊ : ℝ) ∧ (⌊K*a⌋₊ : ℝ) ≤ K*a := by
  constructor
  · have h := Nat.lt_floor_add_one (K*a)
    nlinarith
  · exact Nat.floor_le (mul_nonneg hK ha)

theorem finite_rounding {t : Type} [Fintype t] (β : ℝ) (E : t → ℝ)
    (θ : ℝ) (hθ : 0<θ) (hθ1 : θ<1) :
    ∃ K : ℕ, 0<K ∧ ∀ i,
      0<⌊(K : ℝ)*Real.exp (β*E i)⌋₊ ∧
      (1-θ)*(K : ℝ)*Real.exp (β*E i) ≤ (⌊(K : ℝ)*Real.exp (β*E i)⌋₊ : ℝ) ∧
      (⌊(K : ℝ)*Real.exp (β*E i)⌋₊ : ℝ) ≤ (K : ℝ)*Real.exp (β*E i) := by
  classical
  let a (i : t) := Real.exp (β*E i)
  obtain ⟨K,hK⟩ := exists_nat_gt (1+∑ i,1/(θ*a i))
  have hs : 0≤∑ i,1/(θ*a i) := Finset.sum_nonneg (fun i _ => by positivity)
  have hKr : 0<(K : ℝ) := by linarith
  refine ⟨K,by exact_mod_cast hKr,?_⟩
  intro i
  have hai : 0<a i := Real.exp_pos _
  have hterm : 1/(θ*a i) ≤ ∑ j,1/(θ*a j) := by
    exact Finset.single_le_sum (f:=fun j : t => 1/(θ*a j)) (fun j _ => by positivity) (Finset.mem_univ i)
  have hlt : 1/(θ*a i)<(K : ℝ) := by linarith
  have hbig : 1<θ*(K : ℝ)*a i := by
    have h := (div_lt_iff₀ (mul_pos hθ hai)).mp hlt
    nlinarith
  have hKa : 0≤(K : ℝ)*a i := mul_nonneg hKr.le hai.le
  have hθKa : θ*((K : ℝ)*a i)≤(K : ℝ)*a i := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ1.le hKa
  have hfloor : 0<⌊(K : ℝ)*a i⌋₊ := by
    apply Nat.floor_pos.mpr
    nlinarith
  exact ⟨hfloor,relative_floor (a i) K θ hai.le hKr.le hbig.le⟩

theorem weighted_tile_bounds (β E K θ : ℝ) (g : ℕ)
    (hl : (1-θ)*K*Real.exp (β*E) ≤ (g : ℝ))
    (hu : (g : ℝ) ≤ K*Real.exp (β*E)) :
    (1-θ)*K ≤ (g : ℝ)*Real.exp (-β*E) ∧
      (g : ℝ)*Real.exp (-β*E) ≤ K := by
  have he : Real.exp (β*E)*Real.exp (-β*E)=1 := by
    rw [← Real.exp_add,show β*E+ -β*E=0 by ring,Real.exp_zero]
  constructor
  · have h := mul_le_mul_of_nonneg_right hl (Real.exp_pos (-β*E)).le
    simpa only [mul_assoc,he,mul_one] using h
  · have h := mul_le_mul_of_nonneg_right hu (Real.exp_pos (-β*E)).le
    simpa only [mul_assoc,he,mul_one] using h

theorem normalized_inner_weight {t : Type} [Fintype t] [DecidableEq t] [Nonempty t]
    (I : Finset t) (w : t → ℝ) (K θ : ℝ) (hK : 0<K) (hθ : θ<1)
    (hl : ∀ i,(1-θ)*K≤w i) (hu : ∀ i,w i≤K) :
    (1-θ)*(I.card : ℝ)/(Fintype.card t : ℝ) ≤
      (∑ i ∈ I,w i)/(∑ i,w i) := by
  have ha : 0<(1-θ)*K := mul_pos (sub_pos.mpr hθ) hK
  have hw : ∀ i,0<w i := fun i => ha.trans_le (hl i)
  have htotal : 0<∑ i,w i := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  have htbound : ∑ i,w i ≤ (Fintype.card t : ℝ)*K := by
    simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hu i)
  have hibound : (I.card : ℝ)*((1-θ)*K) ≤ ∑ i ∈ I,w i := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using
      Finset.sum_le_sum (fun i (_ : i ∈ I) => hl i)
  have hcard : 0<(Fintype.card t : ℝ) := by exact_mod_cast Fintype.card_pos
  let a := (1-θ)*(I.card : ℝ)/(Fintype.card t : ℝ)
  have han : 0≤a := div_nonneg (mul_nonneg (sub_pos.mpr hθ).le (by positivity)) hcard.le
  apply (le_div_iff₀ htotal).mpr
  change a*(∑ i,w i)≤_
  calc
    a*(∑ i,w i) ≤ a*((Fintype.card t : ℝ)*K) := mul_le_mul_of_nonneg_left htbound han
    _ = (I.card : ℝ)*((1-θ)*K) := by dsimp [a]; field_simp [ne_of_gt hcard]
    _ ≤ _ := hibound

def coordinateEnergy {n : ℕ} (ω : Fin n → ℝ) (j : Fin n → ℤ) : ℝ :=
  ∑ i,(j i : ℝ)*ω i

theorem coordinateEnergy_add {n : ℕ} (ω : Fin n → ℝ) (j k : Fin n → ℤ) :
    coordinateEnergy ω (j+k)=coordinateEnergy ω j+coordinateEnergy ω k := by
  simp only [coordinateEnergy,Pi.add_apply,Int.cast_add,add_mul,Finset.sum_add_distrib]

theorem coordinate_margin {n : ℕ} (j δ : Fin n → ℤ) (N M : ℤ)
    (hj : ∀ i,|j i|≤N) (hδ : ∀ i,|δ i|≤M) :
    ∀ i,|j i+δ i|≤N+M := by
  intro i
  exact (abs_add_le (j i) (δ i)).trans (add_le_add (hj i) (hδ i))

theorem finite_energy_origin {t : Type} [Fintype t] (E : t → ℝ) :
    ∃ E0 : ℝ,0≤E0 ∧ ∀ i,0≤E0+E i := by
  classical
  refine ⟨∑ i,|E i|,Finset.sum_nonneg (fun i _ => abs_nonneg _),?_⟩
  intro i
  have h : |E i|≤∑ j,|E j| :=
    Finset.single_le_sum (f:=fun j : t => |E j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hn := neg_le_abs (E i)
  linarith

theorem normalized_origin_invariant {t : Type} [Fintype t] [DecidableEq t]
    (I : Finset t) (g : t → ℕ) (E : t → ℝ) (β E0 : ℝ) :
    (∑ i ∈ I,(g i : ℝ)*Real.exp (-β*(E0+E i))) /
        (∑ i,(g i : ℝ)*Real.exp (-β*(E0+E i))) =
      (∑ i ∈ I,(g i : ℝ)*Real.exp (-β*E i)) /
        (∑ i,(g i : ℝ)*Real.exp (-β*E i)) := by
  have he (i : t) : (g i : ℝ)*Real.exp (-β*(E0+E i)) =
      Real.exp (-β*E0)*((g i : ℝ)*Real.exp (-β*E i)) := by
    rw [mul_add,Real.exp_add]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum,← Finset.mul_sum]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

theorem interior_fraction (s m : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ N : ℕ,0<N ∧ 1-ε ≤ ((N : ℝ)/((N : ℝ)+2*m))^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt (1+(s : ℝ)*(2*m)/ε)
  have hterm : 0≤(s : ℝ)*(2*m)/ε := by positivity
  have hNr : 0<(N : ℝ) := by linarith
  have hden : 0<(N : ℝ)+2*m := by positivity
  have hx : 2*(m : ℝ)/((N : ℝ)+2*m)≤1 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hsmall : (s : ℝ)*(2*m)/((N : ℝ)+2*m)<ε := by
    apply (div_lt_iff₀ hden).mpr
    have he := (div_lt_iff₀ hε).mp (lt_of_le_of_lt (by linarith :
      (s : ℝ)*(2*m)/ε ≤ 1+(s : ℝ)*(2*m)/ε) hN)
    have hm : 0≤(2*(m : ℝ))*ε := by positivity
    nlinarith
  have hbern := one_add_mul_le_pow (by linarith : -2≤ -(2*(m : ℝ)/((N : ℝ)+2*m))) s
  have hr : 1+ -(2*(m : ℝ)/((N : ℝ)+2*m)) = (N : ℝ)/((N : ℝ)+2*m) := by
    field_simp
    ring
  rw [hr] at hbern
  refine ⟨N,by exact_mod_cast hNr,?_⟩
  have heq : (s : ℝ)*(2*m/((N : ℝ)+2*m)) = (s : ℝ)*(2*m)/((N : ℝ)+2*m) := by ring
  nlinarith

abbrev Bath {t : Type} (g : t → ℕ) := (i : t) × Fin (g i)

def bathHamiltonian {t : Type} [Fintype t] [DecidableEq t]
    (g : t → ℕ) (E : t → ℝ) : Hamiltonian (Bath g) :=
  FlatMatrix.diagonalHamiltonian (Bath g) (fun b => E b.1)

theorem bath_partition {t : Type} [Fintype t] (g : t → ℕ) (E : t → ℝ) (β : ℝ) :
    (∑ b : Bath g,Real.exp (-β*E b.1)) = ∑ i,(g i : ℝ)*Real.exp (-β*E i) := by
  calc
    _ = ∑ i,∑ _ : Fin (g i),Real.exp (-β*E i) :=
      Fintype.sum_sigma (fun b : Sigma (fun i => Fin (g i)) => Real.exp (-β*E b.1))
    _ = _ := by simp

theorem bath_gibbs {t : Type} [Fintype t] [DecidableEq t]
    (g : t → ℕ) (E : t → ℝ) (β : ℝ) :
    gibbs β (bathHamiltonian g E) = diagonal (fun b : Bath g =>
      ((Real.exp (-β*E b.1)/(∑ i,(g i : ℝ)*Real.exp (-β*E i)) : ℝ) : ℂ)) := by
  unfold bathHamiltonian
  rw [FlatMatrix.diagonal_gibbs,bath_partition]

def goodProjector {t : Type} [Fintype t] [DecidableEq t]
    (g : t → ℕ) (I : Finset t) : Mat (Bath g) :=
  diagonal (fun b => if b.1∈I then 1 else 0)

theorem good_probability {t : Type} [Fintype t] [DecidableEq t]
    (g : t → ℕ) (E : t → ℝ) (β : ℝ) (I : Finset t) :
    energy (goodProjector g I) (gibbs β (bathHamiltonian g E)) =
      (∑ i ∈ I,(g i : ℝ)*Real.exp (-β*E i)) /
        (∑ i,(g i : ℝ)*Real.exp (-β*E i)) := by
  classical
  rw [bath_gibbs]
  simp only [goodProjector,energy,diagonal_mul_diagonal,trace_diagonal,Complex.re_sum]
  have hp (b : Bath g) :
      ((if b.1∈I then 1 else 0 : ℂ) *
        ((Real.exp (-β*E b.1)/(∑ i,(g i : ℝ)*Real.exp (-β*E i)) : ℝ) : ℂ)).re =
      if b.1∈I then Real.exp (-β*E b.1)/(∑ i,(g i : ℝ)*Real.exp (-β*E i)) else 0 := by
    split_ifs <;> simp only [one_mul,zero_mul,Complex.ofReal_re,Complex.zero_re]
  simp_rw [hp]
  have hs := Fintype.sum_sigma (fun b : Sigma (fun i => Fin (g i)) =>
    if b.1∈I then Real.exp (-β*E b.1)/(∑ i,(g i : ℝ)*Real.exp (-β*E i)) else 0)
  rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp_rw [mul_ite,mul_zero,← mul_div_assoc]
  rw [Finset.sum_ite]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter,Finset.sum_const_zero,add_zero]
  rw [Finset.sum_div]

/-- One actual finite Gibbs stock works for every tile event, after an explicit
nonnegative energy-origin shift. All degeneracies are positive integers. -/
theorem rounded_stock {t : Type} [Fintype t] [DecidableEq t] [Nonempty t]
    (β : ℝ) (E : t → ℝ) (θ : ℝ) (hθ : 0<θ) (hθ1 : θ<1) :
    ∃ (K : ℕ) (g : t → ℕ) (E0 : ℝ),0<K ∧ (∀ i,0<g i) ∧
      0≤E0 ∧ (∀ i,0≤E0+E i) ∧ ∀ I : Finset t,
        (1-θ)*(I.card : ℝ)/(Fintype.card t : ℝ) ≤
          energy (goodProjector g I) (gibbs β (bathHamiltonian g (fun i => E0+E i))) := by
  obtain ⟨K,hK,hg⟩ := finite_rounding β E θ hθ hθ1
  obtain ⟨E0,hE0,hE⟩ := finite_energy_origin E
  let g (i : t) := ⌊(K : ℝ)*Real.exp (β*E i)⌋₊
  refine ⟨K,g,E0,hK,fun i => (hg i).1,hE0,hE,?_⟩
  intro I
  rw [good_probability,normalized_origin_invariant]
  apply normalized_inner_weight I (fun i => (g i : ℝ)*Real.exp (-β*E i)) K θ
    (by exact_mod_cast hK) hθ1
  · intro i
    exact (weighted_tile_bounds β (E i) K θ (g i) (hg i).2.1 (hg i).2.2).1
  · intro i
    exact (weighted_tile_bounds β (E i) K θ (g i) (hg i).2.1 (hg i).2.2).2

end ScheduleLaw.Blueprint.SupportTiles
