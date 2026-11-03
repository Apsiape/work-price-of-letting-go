import PhaseMixedHistory
import PhaseHardwareComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseHardwareHistory
open History
variable {I : Inventory} {S : Schedule I} {β : ℝ}
variable (p : Driven S β) {D : ℕ} (hD : 0<D) (φ : Density (Fin D)) (Hφ : Hamiltonian (Fin D))
    (G : Cut S → Mat (Fin (p.extension.b*D) × Payload I))
    (hG : ∀ k,IsUnitary (G k)) (hlocal : ∀ k,LocalOn I (p.extension.b*D) (held S k) (G k))
local notation "q" => PhaseHardware.hardware p hD φ Hφ G hG hlocal
local notation "idle" => IdleExtension.extension p.extension (PhaseHardware.phaseStock hD φ)

/-- The cut estimates are applied only to the exact idle history. The
conclusion is full-state accuracy at every prefix for the actual hardware. -/
theorem from_cut_error (ε : Cut S → ℝ) (hε0 : ∀ k,0≤ε k)
    (hcut : ∀ z (t : Tester S z) (k : Cut S),
      traceDistance (evolve (jointGate (q).extension t k) (run idle t k.val))
        (evolve (jointGate idle t k) (run idle t k.val))≤ε k) :
    PhaseHardwareComparison.Close p hD φ Hφ G hG hlocal (∑ k,ε k) := by
  intro z t n hn
  let U : ℕ → Mat (Global (q).extension z) := fun n =>
    if h : n<2*S.visits+1 then jointGate (q).extension t ⟨n,h⟩ else 1
  let V : ℕ → Mat (Global (q).extension z) := fun n =>
    if h : n<2*S.visits+1 then jointGate idle t ⟨n,h⟩ else 1
  let error : ℕ → ℝ := fun n => if h : n<2*S.visits+1 then ε ⟨n,h⟩ else 0
  have hU (n : ℕ) : IsUnitary (U n) := by
    dsimp only [U]
    split_ifs with h
    · exact jointGate_unitary _ _ _
    · constructor <;> simp
  have hrunU (n : ℕ) : PhaseMixedHistory.run U (initialState idle t) n=run (q).extension t n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [PhaseMixedHistory.run,ih,run]
      dsimp only [U]
      split_ifs <;> simp only [evolve,conjTranspose_one,one_mul,mul_one]
  have hrunV (n : ℕ) : PhaseMixedHistory.run V (initialState idle t) n=run idle t n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [PhaseMixedHistory.run,ih,run]
      dsimp only [V]
      split_ifs <;> simp only [evolve,conjTranspose_one,one_mul,mul_one]
  have hstep (n : ℕ) : traceDistance
      (evolve (U n) (PhaseMixedHistory.run V (initialState idle t) n))
      (evolve (V n) (PhaseMixedHistory.run V (initialState idle t) n))≤error n := by
    rw [hrunV]
    dsimp only [U,V,error]
    split_ifs with h
    · exact hcut z t ⟨n,h⟩
    · simp only [W2.traceDistance_self,le_refl]
  have he := PhaseMixedHistory.telescope U V hU (initialState idle t) error hstep n
  rw [hrunU,hrunV] at he
  apply he.trans
  calc (∑ m∈Finset.range n,error m)≤∑ m∈Finset.range (2*S.visits+1),error m := by
         apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn)
         intro m _ _
         dsimp only [error]
         split_ifs with h
         · exact hε0 ⟨m,h⟩
         · exact le_refl 0
       _ = ∑ k : Cut S,error k.val := (Fin.sum_univ_eq_sum_range error (2*S.visits+1)).symm
       _ = _ := Finset.sum_congr rfl (fun k _ => dif_pos k.isLt)

end ScheduleLaw.Blueprint.PhaseHardwareHistory
