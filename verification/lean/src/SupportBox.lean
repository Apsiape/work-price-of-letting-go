import SupportTiles

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped BigOperators
namespace ScheduleLaw.Blueprint.SupportBox

variable (ι : Type) [Fintype ι] [DecidableEq ι]

abbrev Tile (N : ℕ) := ι → Fin (N+2)

def innerEmbedding (N : ℕ) : (ι → Fin N) ↪ Tile ι N where
  toFun x i := ⟨(x i).val+1,by have h := (x i).isLt; omega⟩
  inj' := by
    intro x y h
    funext i
    apply Fin.ext
    have hh := congrArg (fun z => (z i).val) h
    change (x i).val+1=(y i).val+1 at hh
    omega

def good (N : ℕ) : Finset (Tile ι N) := Finset.univ.map (innerEmbedding ι N)

theorem good_card (N : ℕ) : (good ι N).card = N^(Fintype.card ι) := by
  simp [good]

theorem tile_card (N : ℕ) : Fintype.card (Tile ι N) = (N+2)^(Fintype.card ι) := by
  simp [Tile]

def coordinates {N : ℕ} (j : Tile ι N) : ι → ℤ := fun i => (j i).val

theorem good_coordinate_bounds {N : ℕ} (j : Tile ι N) (hj : j ∈ good ι N) (i : ι) :
    1 ≤ coordinates ι j i ∧ coordinates ι j i ≤ N := by
  obtain ⟨x,_,hx⟩ := Finset.mem_map.mp hj
  subst j
  have hi := (x i).isLt
  change (1 : ℤ) ≤ (((x i).val+1 : ℕ) : ℤ) ∧ (((x i).val+1 : ℕ) : ℤ) ≤ N
  omega

/-- Every shift of at most one coordinate stays inside the full box. -/
theorem good_shift {N : ℕ} (j : Tile ι N) (hj : j ∈ good ι N)
    (v : ι → ℤ) (hv : ∀ i, -1 ≤ v i ∧ v i ≤ 1) :
    ∃ k : Tile ι N, coordinates ι k = coordinates ι j+v := by
  have hb (i : ι) : 0 ≤ coordinates ι j i+v i ∧ coordinates ι j i+v i < N+2 := by
    have h := good_coordinate_bounds ι j hj i
    have hh := hv i
    omega
  let k : Tile ι N := fun i => ⟨(coordinates ι j i+v i).toNat,by have h := hb i; omega⟩
  refine ⟨k,?_⟩
  funext i
  exact Int.toNat_of_nonneg (hb i).1

omit [Fintype ι] [DecidableEq ι] in
theorem coordinates_injective {N : ℕ} : Function.Injective (coordinates ι (N := N)) := by
  intro j k h
  funext i
  apply Fin.ext
  have he := congrFun h i
  dsimp only [coordinates] at he
  exact_mod_cast he

theorem good_ratio (N : ℕ) :
    ((good ι N).card : ℝ)/(Fintype.card (Tile ι N) : ℝ) =
      ((N : ℝ)/((N : ℝ)+2))^(Fintype.card ι) := by
  rw [good_card,tile_card,div_pow]
  push_cast
  rfl

/-- The rounded stock retains its actual degeneracy bounds, as well as the
 normalized event estimate, for subsequent shell-count injections. -/
theorem rounded_stock_bounds {t : Type} [Fintype t] [DecidableEq t] [Nonempty t]
    (β : ℝ) (E : t → ℝ) (θ : ℝ) (hθ : 0<θ) (hθ1 : θ<1) :
    ∃ (K : ℕ) (g : t → ℕ) (E0 : ℝ), 0<K ∧ (∀ i,0<g i) ∧
      (∀ i,(1-θ)*(K : ℝ)*Real.exp (β*E i) ≤ (g i : ℝ) ∧
        (g i : ℝ) ≤ (K : ℝ)*Real.exp (β*E i)) ∧
      0≤E0 ∧ (∀ i,0≤E0+E i) ∧ ∀ I : Finset t,
        (1-θ)*(I.card : ℝ)/(Fintype.card t : ℝ) ≤
          energy (SupportTiles.goodProjector g I)
            (gibbs β (SupportTiles.bathHamiltonian g (fun i => E0+E i))) := by
  obtain ⟨K,hK,hg⟩ := SupportTiles.finite_rounding β E θ hθ hθ1
  obtain ⟨E0,hE0,hE⟩ := SupportTiles.finite_energy_origin E
  let g (i : t) := ⌊(K : ℝ)*Real.exp (β*E i)⌋₊
  refine ⟨K,g,E0,hK,fun i => (hg i).1,fun i => (hg i).2,hE0,hE,?_⟩
  intro I
  rw [SupportTiles.good_probability,SupportTiles.normalized_origin_invariant]
  apply SupportTiles.normalized_inner_weight I
    (fun i => (g i : ℝ)*Real.exp (-β*E i)) K θ (by exact_mod_cast hK) hθ1
  · intro i
    exact (SupportTiles.weighted_tile_bounds β (E i) K θ (g i) (hg i).2.1 (hg i).2.2).1
  · intro i
    exact (SupportTiles.weighted_tile_bounds β (E i) K θ (g i) (hg i).2.1 (hg i).2.2).2

end ScheduleLaw.Blueprint.SupportBox
