import FiniteConverterModel
/-! Coordinate swaps on all columns, including unmatched and boundary columns. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open scoped Classical
open Matrix
open scoped BigOperators ComplexOrder
namespace ScheduleLaw.Blueprint.FiniteSwap
variable {A O : Type} (s t : A → O)

def apply (x : O) : O :=
  if hs : ∃ a, s a=x then t (Classical.choose hs)
  else if ht : ∃ a, t a=x then s (Classical.choose ht) else x

lemma on_source (hs : Function.Injective s) (a : A) : apply s t (s a)=t a := by
  have he : ∃ b, s b=s a := ⟨a,rfl⟩
  rw [apply,dif_pos he]
  exact congrArg t (hs (Classical.choose_spec he))
lemma on_target (ht : Function.Injective t) (hd : ∀ a b,s a ≠ t b) (a : A) : apply s t (t a)=s a := by
  have hn : ¬∃ b, s b=t a := by rintro ⟨b,h⟩; exact hd b a h
  have he : ∃ b, t b=t a := ⟨a,rfl⟩
  rw [apply,dif_neg hn,dif_pos he]
  exact congrArg s (ht (Classical.choose_spec he))
lemma outside (x : O) (hS : ¬∃ a,s a=x) (hT : ¬∃ a,t a=x) : apply s t x=x := by
  rw [apply,dif_neg hS,dif_neg hT]
variable (hs : Function.Injective s) (ht : Function.Injective t)
  (hd : ∀ a b,s a ≠ t b)
include hs ht hd
lemma involutive : Function.Involutive (apply s t) := by
  intro x
  by_cases hS : ∃ a,s a=x
  · obtain ⟨a,rfl⟩:=hS
    rw [on_source s t hs,on_target s t ht hd]
  · by_cases hT : ∃ a,t a=x
    · obtain ⟨a,rfl⟩:=hT
      rw [on_target s t ht hd,on_source s t hs]
    · rw [outside s t x hS hT,outside s t x hS hT]

def permutation : Equiv.Perm O := ⟨apply s t,apply s t,involutive s t hs ht hd,involutive s t hs ht hd⟩
lemma permutation_symm : (permutation s t hs ht hd).symm=permutation s t hs ht hd := rfl
lemma energy_invariant (E : O → ℝ) (he : ∀ a,E (t a)=E (s a)) (x : O) :
    E (permutation s t hs ht hd x)=E x := by
  change E (apply s t x)=E x
  by_cases hS : ∃ a,s a=x
  · obtain ⟨a,rfl⟩:=hS
    rw [on_source s t hs,he]
  · by_cases hT : ∃ a,t a=x
    · obtain ⟨a,rfl⟩:=hT
      rw [on_target s t ht hd,he]
    · rw [outside s t x hS hT]

variable [Fintype O] [DecidableEq O]
lemma unitary : IsUnitary ((permutation s t hs ht hd).permMatrix ℂ) :=
  Recorder.permutation_unitary _
lemma diagonal_evolution (p : O → ℂ) :
    evolve ((permutation s t hs ht hd).permMatrix ℂ) (diagonal p) =
      diagonal (fun x => p (permutation s t hs ht hd x)) := by
  rw [Recorder.permutation_evolve]
  ext i j
  by_cases h : i=j
  · subst j; simp
  · simp [Matrix.diagonal,h,(permutation s t hs ht hd).injective.ne h]
lemma conserves (E : O → ℝ) (he : ∀ a,E (t a)=E (s a)) :
    Conserves ((permutation s t hs ht hd).permMatrix ℂ) (diagonal (fun x => (E x : ℂ))) := by
  have hstar : ((permutation s t hs ht hd).permMatrix ℂ)ᴴ =
      (permutation s t hs ht hd).permMatrix ℂ := by
    rw [conjTranspose_permMatrix]
    rfl
  unfold Conserves
  rw [hstar]
  have hv := diagonal_evolution s t hs ht hd (fun x => (E x : ℂ))
  unfold evolve at hv
  rw [hstar] at hv
  rw [hv]
  ext i j
  simp only [energy_invariant s t hs ht hd E he]
end ScheduleLaw.Blueprint.FiniteSwap
