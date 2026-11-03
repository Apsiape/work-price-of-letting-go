import SupportStock

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace ScheduleLaw.Blueprint.SupportShells

/-- Strict partition-function slack bounds the actual finite integer counts
 in a shell; every source column is counted, rather than only average inputs. -/
theorem shell_count_lt {a b : Type} [Fintype a] [Fintype b]
    (ES : a → ℝ) (ET : b → ℝ) (ns : a → ℕ) (nt : b → ℕ)
    (β K θ u x : ℝ) (hK : 0<K)
    (hs : ∀ i,(ns i : ℝ) ≤ K*Real.exp (β*(u-ES i)))
    (ht : ∀ i,(1-θ)*K*Real.exp (β*(u-x-ET i)) ≤ (nt i : ℝ))
    (hcap : (∑ i,Real.exp (-β*ES i)) <
      (1-θ)*Real.exp (-β*x)*(∑ i,Real.exp (-β*ET i))) :
    (∑ i,ns i) < ∑ i,nt i := by
  have hsource : (∑ i,(ns i : ℝ)) ≤
      K*Real.exp (β*u)*(∑ i,Real.exp (-β*ES i)) := by
    calc _ ≤ ∑ i,K*Real.exp (β*(u-ES i)) := Finset.sum_le_sum (fun i _ => hs i)
         _ = _ := by
           rw [Finset.mul_sum]
           apply Finset.sum_congr rfl
           intro i _
           rw [mul_assoc,← Real.exp_add]
           congr 2
           ring
  have htarget : (1-θ)*K*Real.exp (β*(u-x))*(∑ i,Real.exp (-β*ET i)) ≤
      ∑ i,(nt i : ℝ) := by
    calc _ = ∑ i,(1-θ)*K*Real.exp (β*(u-x-ET i)) := by
           rw [Finset.mul_sum]
           apply Finset.sum_congr rfl
           intro i _
           rw [mul_assoc,← Real.exp_add]
           congr 2
           ring
         _ ≤ _ := Finset.sum_le_sum (fun i _ => ht i)
  have hstrict := mul_lt_mul_of_pos_left hcap (mul_pos hK (Real.exp_pos (β*u)))
  have he : K*Real.exp (β*u)*((1-θ)*Real.exp (-β*x)*(∑ i,Real.exp (-β*ET i))) =
      (1-θ)*K*Real.exp (β*(u-x))*(∑ i,Real.exp (-β*ET i)) := by
    have hexp : Real.exp (β*(u-x)) = Real.exp (β*u)*Real.exp (-β*x) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hexp]
    ring
  rw [he] at hstrict
  exact_mod_cast hsource.trans_lt (hstrict.trans_le htarget)

/-- An actual finite injection, with all degeneracy labels present. -/
theorem counted_shell_injection {a b : Type} [Fintype a] [Fintype b]
    (ES : a → ℝ) (ET : b → ℝ) (ns : a → ℕ) (nt : b → ℕ)
    (β K θ u x : ℝ) (hK : 0<K)
    (hs : ∀ i,(ns i : ℝ) ≤ K*Real.exp (β*(u-ES i)))
    (ht : ∀ i,(1-θ)*K*Real.exp (β*(u-x-ET i)) ≤ (nt i : ℝ))
    (hcap : (∑ i,Real.exp (-β*ES i)) <
      (1-θ)*Real.exp (-β*x)*(∑ i,Real.exp (-β*ET i))) :
    Nonempty ((Sigma (fun i => Fin (ns i))) ↪ Sigma (fun i => Fin (nt i))) := by
  apply Function.Embedding.nonempty_of_card_le
  simp only [Fintype.card_sigma,Fintype.card_fin]
  exact (shell_count_lt ES ET ns nt β K θ u x hK hs ht hcap).le

/-- Assemble independent shell injections without identifying equal-energy
 coordinate labels. The result preserves the literal total-shell label. -/
theorem fiberwise_injection {a b c : Type} [Fintype a] [Fintype b] [DecidableEq c]
    (sa : a → c) (tb : b → c)
    (hc : ∀ z,Fintype.card {i : a // sa i=z} ≤ Fintype.card {j : b // tb j=z}) :
    ∃ f : a ↪ b, ∀ i,tb (f i)=sa i := by
  classical
  let e (z : c) : {i : a // sa i=z} ↪ {j : b // tb j=z} :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (hc z))
  let f : a ↪ b := (Equiv.sigmaFiberEquiv sa).symm.toEmbedding.trans
    ((Function.Embedding.sigmaMap (Function.Embedding.refl c) e).trans
      (Equiv.sigmaFiberEquiv tb).toEmbedding)
  refine ⟨f,?_⟩
  intro i
  exact (e (sa i) ⟨i,rfl⟩).property

end ScheduleLaw.Blueprint.SupportShells
