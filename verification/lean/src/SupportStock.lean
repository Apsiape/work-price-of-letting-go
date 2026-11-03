import SupportBox

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped BigOperators
namespace ScheduleLaw.Blueprint.SupportStock

/-- A literal inner-box Gibbs event with all rounded multiplicities retained.
 These are the same counts subsequently compared within energy shells. -/
theorem prepared_stock (s : ℕ) (ω : Fin s → ℝ) (β ZP ZQ x f : ℝ)
    (hβ : 0<β) (hP : 0<ZP) (hQ : 0<ZQ)
    (hx : x<Real.log (ZQ/ZP)/β) (hf : 0<f) :
    ∃ (θ : ℝ) (N K : ℕ) (g : SupportBox.Tile (Fin s) N → ℕ) (E0 : ℝ),
      0<θ ∧ θ<1 ∧ 0<N ∧ 0<K ∧ (∀ j,0<g j) ∧
      (∀ j,(1-θ)*(K : ℝ)*Real.exp (β*SupportTiles.coordinateEnergy ω (SupportBox.coordinates (Fin s) j))
        ≤ (g j : ℝ) ∧ (g j : ℝ) ≤
        (K : ℝ)*Real.exp (β*SupportTiles.coordinateEnergy ω (SupportBox.coordinates (Fin s) j))) ∧
      ZP<(1-θ)*Real.exp (-β*x)*ZQ ∧ 0≤E0 ∧
      (∀ j : SupportBox.Tile (Fin s) N,0≤E0+SupportTiles.coordinateEnergy ω (SupportBox.coordinates (Fin s) j)) ∧
      1-f ≤ energy (SupportTiles.goodProjector g (SupportBox.good (Fin s) N))
        (gibbs β (SupportTiles.bathHamiltonian g (fun j =>
          E0+SupportTiles.coordinateEnergy ω (SupportBox.coordinates (Fin s) j)))) := by
  obtain ⟨θ0,hθ0,hθ01,hcap⟩ := SupportTiles.strict_capacity_margin β ZP ZQ x hβ hP hQ hx
  let θ := min θ0 (min (f/2) (1/2))
  have hθ : 0<θ := lt_min hθ0 (lt_min (by positivity) (by norm_num))
  have hθle : θ ≤ θ0 := min_le_left _ _
  have hθf : θ ≤ f/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hθ1 : θ<1 := hθle.trans_lt hθ01
  have hcapacity : ZP<(1-θ)*Real.exp (-β*x)*ZQ := by
    apply hcap.trans_le
    gcongr
  obtain ⟨N,hN,hfrac⟩ := SupportTiles.interior_fraction s 1 (f/2) (by positivity)
  let E (j : SupportBox.Tile (Fin s) N) :=
    SupportTiles.coordinateEnergy ω (SupportBox.coordinates (Fin s) j)
  obtain ⟨K,g,E0,hK,hg,hbounds,hE0,hE,hprob⟩ :=
    SupportBox.rounded_stock_bounds β E θ hθ hθ1
  refine ⟨θ,N,K,g,E0,hθ,hθ1,hN,hK,hg,hbounds,hcapacity,hE0,hE,?_⟩
  let q : ℝ := ((SupportBox.good (Fin s) N).card : ℝ)/
    (Fintype.card (SupportBox.Tile (Fin s) N) : ℝ)
  have hq0 : 0≤q := by positivity
  have hden : 0<(Fintype.card (SupportBox.Tile (Fin s) N) : ℝ) := by
    rw [SupportBox.tile_card]
    positivity
  have hq1 : q ≤ 1 := by
    apply (div_le_one hden).mpr
    exact_mod_cast Finset.card_le_card (Finset.subset_univ (SupportBox.good (Fin s) N))
  have hq : 1-f/2 ≤ q := by
    dsimp only [q]
    rw [SupportBox.good_ratio]
    simpa only [Fintype.card_fin,Nat.cast_one,mul_one] using hfrac
  have hproduct : 1-f ≤ (1-θ)*q := by
    have hθq : θ*q ≤ θ := by nlinarith
    nlinarith
  have hstock := hprob (SupportBox.good (Fin s) N)
  exact hproduct.trans (by simpa only [q,mul_div_assoc] using hstock)

end ScheduleLaw.Blueprint.SupportStock
