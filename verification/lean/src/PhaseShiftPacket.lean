import PhaseProductVectors
import PhasePacketDensity

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace ScheduleLaw.Blueprint.PhaseShiftPacket
open PhaseVectorDistance PhaseSinePacket PhaseLatticeBox
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def raw (L : ℕ) (x : PhaseLatticeBox.Lattice ι) : ℂ := ∏ i,(W2.sineValue L (x i) : ℂ)

theorem raw_support (L : ℕ) (x : PhaseLatticeBox.Lattice ι) (hx : raw L x≠0) :
    ∀ i,0≤x i ∧ x i<(L : ℤ) := by
  intro i
  have hi : (W2.sineValue L (x i) : ℂ)≠0 := (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ _)
  by_contra h
  apply hi
  simp only [W2.sineValue,if_neg h,Complex.ofReal_zero]

theorem raw_outside (L : ℕ) (x : PhaseLatticeBox.Lattice ι) (hx : x∉box ι L) : raw L x=0 := by
  by_contra hn
  apply hx
  apply (box_mem _ _).mpr
  intro i
  have hi := raw_support L x hn i
  omega

theorem scalar_square_sum (L : ℕ) (hL : 0<L) (δ : ℤ) (hδ : -1≤δ ∧ δ≤1) :
    (∑ j : Fin (L+4),(W2.sineValue L ((j.val : ℤ)-2-δ))^2)=1 := by
  have hn := EuclideanSpace.norm_sq_eq (vector (scalar L δ))
  rw [scalar_norm L hL δ hδ,one_pow] at hn
  simpa only [vector,PhaseSinePacket.scalar,PiLp.toLp_apply,Complex.norm_real,Real.norm_eq_abs,sq_abs] using hn.symm

theorem scalar_difference_square (L : ℕ) (hL : 0<L) (δ : ℤ) (hδ : -1≤δ ∧ δ≤1) :
    (∑ j : Fin (L+4),(W2.sineValue L ((j.val : ℤ)-2-δ)-W2.sineValue L ((j.val : ℤ)-2))^2)≤
      (Real.pi/(L+1 : ℝ))^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (scalar_difference L hL δ hδ) 2
  rw [EuclideanSpace.norm_sq_eq] at h
  simpa only [vector,PhaseSinePacket.scalar,PiLp.sub_apply,PiLp.toLp_apply,sub_zero,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs,sq_abs] using h

theorem translated_difference (L : ℕ) (hL : 0<L) (δ : PhaseLatticeBox.Lattice ι)
    (hδ : ∀ i,-1≤δ i ∧ δ i≤1) :
    ‖vector (fun x : ↥(box ι L) => raw L (x.val-δ))-
      vector (PhasePacketDensity.packet L)‖≤((Fintype.card ι : ℝ)+1)*Real.pi/(L+1 : ℝ) := by
  let u (i : ι) (j : Fin (L+4)) := W2.sineValue L ((j.val : ℤ)-2-δ i)
  let v (_i : ι) (j : Fin (L+4)) := W2.sineValue L ((j.val : ℤ)-2)
  have hu (i : ι) : (∑ j,u i j^2)=1 := scalar_square_sum L hL (δ i) (hδ i)
  have hv (i : ι) : (∑ j,v i j^2)=1 := by simpa only [v,sub_zero] using scalar_square_sum L hL 0 (by omega)
  have hd (i : ι) : (∑ j,(u i j-v i j)^2)≤(Real.pi/(L+1 : ℝ))^2 := scalar_difference_square L hL (δ i) (hδ i)
  have hh := PhaseProductVectors.norm_difference u v hu hv (Real.pi/(L+1 : ℝ)) (by positivity) hd
  have he := PhaseProductOverlap.norm_reindex (boxFrame (ι:=ι) L)
    (fun x : ↥(box ι L) => raw L (x.val-δ)-PhasePacketDensity.packet L x)
  change ‖vector (fun x : ↥(box ι L) => raw L (x.val-δ)-PhasePacketDensity.packet L x)‖≤_
  rw [← he]
  simpa only [u,v,PhaseProductVectors.product,raw,PhasePacketDensity.packet,boxFrame,
    Equiv.coe_fn_mk,Pi.sub_apply,Complex.ofReal_prod,mul_div_assoc] using hh

theorem label_delta (i j k : ι) : -1≤(label j-label i) k ∧ (label j-label i) k≤1 := by
  simp only [label,Pi.sub_apply]
  split_ifs <;> norm_num

end ScheduleLaw.Blueprint.PhaseShiftPacket
