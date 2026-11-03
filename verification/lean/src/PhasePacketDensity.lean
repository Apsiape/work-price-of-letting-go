import PhaseSinePacket
import PhaseLatticeBox
import W2.TensorFamily

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators ComplexOrder
namespace ScheduleLaw.Blueprint.PhasePacketDensity
open PhaseVectorDistance PhaseSinePacket PhaseLatticeBox
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def scalarDensity (L : ℕ) (hL : 0<L) : Density (Fin (L+4)) :=
  ⟨pureMatrix (scalar L 0),pureMatrix_positive _,by
    rw [pureMatrix_trace,normalized_sum _ (scalar_norm L hL 0 (by omega))]
    norm_num⟩

def packet (L : ℕ) (x : ↥(box ι L)) : ℂ := ∏ i,(W2.sineValue L (x.val i) : ℂ)

def density (L : ℕ) (hL : 0<L) : Density ↥(box ι L) :=
  let ρ := W2.tensorFamilyDensity (fun _ : ι => scalarDensity L hL)
  ⟨ρ.matrix.submatrix (boxFrame L).symm (boxFrame L).symm,
    ρ.positive.submatrix _,by rw [submatrix_trace_equiv]; exact ρ.normalized⟩

theorem matrix (L : ℕ) (hL : 0<L) : (density (ι:=ι) L hL).matrix=pureMatrix (packet L) := by
  ext x y
  obtain ⟨u,rfl⟩ := (boxFrame (ι:=ι) L).surjective x
  obtain ⟨v,rfl⟩ := (boxFrame (ι:=ι) L).surjective y
  simp only [density,submatrix_apply,Equiv.symm_apply_apply]
  simp only [W2.tensorFamilyDensity,W2.tensorFamily,scalarDensity,pureMatrix,packet,
    boxFrame,Equiv.coe_fn_mk,PhaseSinePacket.scalar,sub_zero,map_prod,star_prod,← Finset.prod_mul_distrib]


theorem normalized (L : ℕ) (hL : 0<L) : (∑ x,Complex.normSq (packet (ι:=ι) L x))=1 := by
  have hn := (density (ι:=ι) L hL).normalized
  rw [matrix,pureMatrix_trace] at hn
  exact_mod_cast hn

theorem norm (L : ℕ) (hL : 0<L) : ‖vector (packet (ι:=ι) L)‖=1 := by
  have hs := normalized (ι:=ι) L hL
  have hn : ‖vector (packet (ι:=ι) L)‖^2=1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa only [vector,PiLp.toLp_apply,Complex.normSq_eq_norm_sq] using hs
  nlinarith [norm_nonneg (vector (packet (ι:=ι) L))]

theorem entropy_zero (L : ℕ) (hL : 0<L) : entropy (density (ι:=ι) L hL).matrix=0 := by
  rw [matrix]
  exact pure_entropy _ (norm L hL)

theorem supported_interior (L : ℕ) (x : ↥(box ι L)) (hx : packet L x≠0) :
    ∀ i,0≤x.val i ∧ x.val i<(L : ℤ) := by
  intro i
  have hi : (W2.sineValue L (x.val i) : ℂ)≠0 :=
    (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ _)
  by_contra h
  apply hi
  simp only [W2.sineValue,if_neg h,Complex.ofReal_zero]

end ScheduleLaw.Blueprint.PhasePacketDensity
