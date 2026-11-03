import SupportLattice
import SupportSwapEffect

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open scoped Classical
open Matrix
open scoped BigOperators ComplexOrder
namespace ScheduleLaw.Blueprint.SupportTiledGate

def frameEnergy {d s N : ℕ} (ω : Fin s → ℝ) (ds dt : Fin d → (Fin s → ℤ))
    (dx : Fin s → ℤ) (g : SupportBox.Tile (Fin s) N → ℕ) (E0 : ℝ)
    (z : Fin d × (Fin 2 × SupportTiles.Bath g)) : ℝ :=
  (if z.2.1=0 then SupportTiles.coordinateEnergy ω (ds z.1)
    else SupportTiles.coordinateEnergy ω (dt z.1)+SupportTiles.coordinateEnergy ω dx)+E0+
      SupportTiles.coordinateEnergy ω (SupportBox.coordinates (Fin s) z.2.2.1)

/-- The finite lattice injection gives an actual full square conserving gate
 and the initialized good-subspace operator bound, including unused columns. -/
theorem conserving_gate (d s N K : ℕ) (ω : Fin s → ℝ)
    (ds dt : Fin d → (Fin s → ℤ)) (dx : Fin s → ℤ)
    (Ts Tt : Finset (Fin d)) (g : SupportBox.Tile (Fin s) N → ℕ)
    (β θ E0 : ℝ) (hK : 0<K)
    (hg : ∀ j,(1-θ)*(K : ℝ)*Real.exp (β*SupportTiles.coordinateEnergy ω (SupportBox.coordinates (Fin s) j))
      ≤ (g j : ℝ) ∧ (g j : ℝ) ≤
      (K : ℝ)*Real.exp (β*SupportTiles.coordinateEnergy ω (SupportBox.coordinates (Fin s) j)))
    (hshift : ∀ i j k,-1 ≤ ds i k-dt j k-dx k ∧ ds i k-dt j k-dx k ≤ 1)
    (hcap : (∑ i : {i : Fin d // i ∈ Ts},Real.exp (-β*SupportTiles.coordinateEnergy ω (ds i))) <
      (1-θ)*Real.exp (-β*SupportTiles.coordinateEnergy ω dx)*
        (∑ i : {i : Fin d // i ∈ Tt},Real.exp (-β*SupportTiles.coordinateEnergy ω (dt i)))) :
    ∃ U : Mat (Fin d × (Fin 2 × SupportTiles.Bath g)), IsUnitary U ∧
      Conserves U (diagonal (fun z => (frameEnergy ω ds dt dx g E0 z : ℂ))) ∧
      (Uᴴ*diagonal (fun z : Fin d × (Fin 2 × SupportTiles.Bath g) => if z.2.1=1 ∧ z.1 ∈ Tt then 1 else 0)*U -
        diagonal (fun z : Fin d × (Fin 2 × SupportTiles.Bath g) => if z.1 ∈ Ts ∧ z.2.1=0 ∧ z.2.2.1 ∈ SupportBox.good (Fin s) N
          then 1 else 0)).PosSemidef := by
  obtain ⟨f,hf⟩ := SupportLattice.tiled_shell_injection s N K ω
    (fun i : {i : Fin d // i ∈ Ts} => ds i)
    (fun i : {i : Fin d // i ∈ Tt} => dt i) dx g β θ hK hg
    (fun i j k => hshift i j k) hcap
  let scol (z : SupportLattice.Source {i : Fin d // i ∈ Ts} g) :
      Fin d × (Fin 2 × SupportTiles.Bath g) := (z.1.val,(0,z.2.val))
  let tcol (z : SupportLattice.Source {i : Fin d // i ∈ Ts} g) :
      Fin d × (Fin 2 × SupportTiles.Bath g) := ((f z).1.val,(1,(f z).2))
  have hs : Function.Injective scol := by
    intro z w h
    apply Prod.ext
    · apply Subtype.ext; exact congrArg (fun j => j.1) h
    · apply Subtype.ext; exact congrArg (fun j => j.2.2) h
  have ht : Function.Injective tcol := by
    intro z w h
    apply f.injective
    apply Prod.ext
    · apply Subtype.ext; exact congrArg (fun j => j.1) h
    · exact congrArg (fun j => j.2.2) h
  have hd : ∀ z w,scol z ≠ tcol w := by
    intro z w h
    have hb := congrArg (fun j => j.2.1) h
    change (0 : Fin 2)=1 at hb
    exact Fin.zero_ne_one hb
  have he (z : SupportLattice.Source {i : Fin d // i ∈ Ts} g) :
      frameEnergy ω ds dt dx g E0 (tcol z)=frameEnergy ω ds dt dx g E0 (scol z) := by
    have h := congrArg (SupportTiles.coordinateEnergy ω) (hf z)
    rw [SupportTiles.coordinateEnergy_add,SupportTiles.coordinateEnergy_add,
      SupportTiles.coordinateEnergy_add] at h
    simp [frameEnergy,scol,tcol]
    linarith
  obtain ⟨U,hU,hcon,hgap⟩ := SupportSwapEffect.conserving_swap_effect scol tcol hs ht hd
    (frameEnergy ω ds dt dx g E0) he (fun z => z.2.1=1 ∧ z.1 ∈ Tt)
    (fun z => ⟨rfl,(f z).1.property⟩)
  have hrange (j : Fin d × (Fin 2 × SupportTiles.Bath g)) :
      (∃ z,scol z=j) ↔ j.1 ∈ Ts ∧ j.2.1=0 ∧ j.2.2.1 ∈ SupportBox.good (Fin s) N := by
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨z.1.property,rfl,z.2.property⟩
    · rcases j with ⟨i,⟨w,b⟩⟩
      rintro ⟨hi,hw,hb⟩
      change w=0 at hw
      subst w
      exact ⟨(⟨i,hi⟩,⟨b,hb⟩),rfl⟩
  refine ⟨U,hU,hcon,?_⟩
  simp only [hrange] at hgap
  convert hgap using 1 <;> congr!

end ScheduleLaw.Blueprint.SupportTiledGate
