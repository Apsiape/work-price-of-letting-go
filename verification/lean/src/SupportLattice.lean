import SupportFiberCounts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
open scoped BigOperators
namespace ScheduleLaw.Blueprint.SupportLattice

abbrev Source (a : Type) {s N : ℕ} (g : SupportBox.Tile (Fin s) N → ℕ) :=
  a × {b : SupportTiles.Bath g // b.1 ∈ SupportBox.good (Fin s) N}
abbrev Target (b : Type) {s N : ℕ} (g : SupportBox.Tile (Fin s) N → ℕ) := b × SupportTiles.Bath g

/-- Literal finite columns in the same coordinate shell admit an injection.
 Equal real energies at different coordinate labels are kept distinct. -/
theorem tiled_shell_injection {a b : Type} [Fintype a] [Fintype b]
    (s N K : ℕ) (ω : Fin s → ℝ) (ds : a → (Fin s → ℤ))
    (dt : b → (Fin s → ℤ)) (dx : Fin s → ℤ)
    (g : SupportBox.Tile (Fin s) N → ℕ) (β θ : ℝ) (hK : 0<K)
    (hg : ∀ j,(1-θ)*(K : ℝ)*Real.exp (β*SupportTiles.coordinateEnergy ω (SupportBox.coordinates (Fin s) j))
      ≤ (g j : ℝ) ∧ (g j : ℝ) ≤
      (K : ℝ)*Real.exp (β*SupportTiles.coordinateEnergy ω (SupportBox.coordinates (Fin s) j)))
    (hshift : ∀ i j k,-1 ≤ ds i k-dt j k-dx k ∧ ds i k-dt j k-dx k ≤ 1)
    (hcap : (∑ i,Real.exp (-β*SupportTiles.coordinateEnergy ω (ds i))) <
      (1-θ)*Real.exp (-β*SupportTiles.coordinateEnergy ω dx)*
        (∑ i,Real.exp (-β*SupportTiles.coordinateEnergy ω (dt i)))) :
    ∃ f : Source a g ↪ Target b g, ∀ z,
      SupportBox.coordinates (Fin s) (f z).2.1+dt (f z).1+dx =
        SupportBox.coordinates (Fin s) z.2.1.1+ds z.1 := by
  classical
  let cs := SupportBox.coordinates (Fin s) (N := N)
  let es := SupportTiles.coordinateEnergy ω
  let ls (z : Source a g) := cs z.2.1.1+ds z.1
  let lt (z : Target b g) := cs z.2.1+dt z.1+dx
  apply SupportShells.fiberwise_injection ls lt
  intro u
  by_cases hnon : Nonempty {z : Source a g // ls z=u}
  · obtain ⟨⟨z,hzu⟩⟩ := hnon
    let ns (i : a) := Fintype.card {b : SupportTiles.Bath g //
      b.1 ∈ SupportBox.good (Fin s) N ∧ cs b.1+ds i=u}
    let nt (i : b) := Fintype.card {b : SupportTiles.Bath g // cs b.1+dt i+dx=u}
    have hsource : Fintype.card {z : Source a g // ls z=u} = ∑ i,ns i := by
      let e : {z : Source a g // ls z=u} ≃
          {x : a × SupportTiles.Bath g // x.2.1 ∈ SupportBox.good (Fin s) N ∧ cs x.2.1+ds x.1=u} := {
        toFun := fun z => ⟨(z.1.1,z.1.2.1),z.1.2.2,z.2⟩
        invFun := fun z => ⟨(z.1.1,⟨z.1.2,z.2.1⟩),z.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
      rw [Fintype.card_congr e]
      convert SupportFiberCounts.system_bath_fiber_count g
        (fun i j => j ∈ SupportBox.good (Fin s) N ∧ cs j+ds i=u) using 1 <;> congr!
    have htarget : Fintype.card {z : Target b g // lt z=u} = ∑ i,nt i := by
      convert SupportFiberCounts.system_bath_fiber_count g (fun i j => cs j+dt i+dx=u) using 1 <;> congr!
    have hs (i : a) : (ns i : ℝ) ≤ (K : ℝ)*Real.exp (β*(es u-es (ds i))) := by
      have hinj : Function.Injective (fun j : SupportBox.Tile (Fin s) N => cs j+ds i) := by
        intro j k hjk
        apply SupportBox.coordinates_injective (Fin s)
        exact add_right_cancel hjk
      have hnum (j : SupportBox.Tile (Fin s) N) (_hj : j ∈ SupportBox.good (Fin s) N)
          (hju : cs j+ds i=u) : (g j : ℝ) ≤ (K : ℝ)*Real.exp (β*(es u-es (ds i))) := by
        have he : es (cs j)=es u-es (ds i) := by
          have h := congrArg es hju
          change SupportTiles.coordinateEnergy ω (cs j+ds i)=es u at h
          rw [SupportTiles.coordinateEnergy_add] at h
          change es (cs j)+es (ds i)=es u at h
          linarith
        have hgj : (g j : ℝ) ≤ (K : ℝ)*Real.exp (β*es (cs j)) := (hg j).2
        rw [he] at hgj
        exact hgj
      have hraw := SupportFiberCounts.bath_fiber_upper g
        (fun j => j ∈ SupportBox.good (Fin s) N) (fun j => cs j+ds i) hinj u
        ((K : ℝ)*Real.exp (β*(es u-es (ds i)))) (by positivity) hnum
      convert hraw using 1 <;> congr!
    have ht (i : b) : (1-θ)*(K : ℝ)*Real.exp (β*(es u-es dx-es (dt i))) ≤ (nt i : ℝ) := by
      obtain ⟨j,hj⟩ := SupportBox.good_shift (Fin s) z.2.1.1 z.2.2
        (ds z.1-dt i-dx) (fun k => hshift z.1 i k)
      have hju : cs j+dt i+dx=u := by
        change cs j=cs z.2.1.1+(ds z.1-dt i-dx) at hj
        rw [hj]
        change cs z.2.1.1+ds z.1=u at hzu
        rw [← hzu]
        abel
      have he : es (cs j)=es u-es dx-es (dt i) := by
        have h := congrArg es hju
        change SupportTiles.coordinateEnergy ω (cs j+dt i+dx)=es u at h
        rw [SupportTiles.coordinateEnergy_add,SupportTiles.coordinateEnergy_add] at h
        change es (cs j)+es (dt i)+es dx=es u at h
        linarith
      have hc : g j ≤ nt i := by
        convert SupportFiberCounts.bath_fiber_lower g (fun j => cs j+dt i+dx=u) j hju using 1 <;> congr!
      have hgj : (1-θ)*(K : ℝ)*Real.exp (β*es (cs j)) ≤ (g j : ℝ) := (hg j).1
      rw [he] at hgj
      calc _ ≤ (g j : ℝ) := hgj
           _ ≤ _ := by exact_mod_cast hc
    rw [hsource,htarget]
    exact (SupportShells.shell_count_lt (fun i => es (ds i)) (fun i => es (dt i)) ns nt
      β K θ (es u) (es dx) (by exact_mod_cast hK) hs ht hcap).le
  · haveI : IsEmpty {z : Source a g // ls z=u} := not_nonempty_iff.mp hnon
    simp

end ScheduleLaw.Blueprint.SupportLattice
