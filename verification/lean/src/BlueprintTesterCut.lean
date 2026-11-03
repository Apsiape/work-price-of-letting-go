import BlueprintContracts
import BlueprintUnitaryCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

theorem localRegisterGate_mul (I : Inventory) (r : ℕ) (A : Finset (Fin I.count))
    (U V : Mat (Fin r × Restricted I A)) :
    localRegisterGate I r A (U*V) = localRegisterGate I r A U * localRegisterGate I r A V := by
  unfold localRegisterGate
  rw [submatrix_mul_equiv, ← mul_kronecker_mul, one_mul]

theorem localOn_mul (I : Inventory) (r : ℕ) (A : Finset (Fin I.count))
    (U V : Mat (Fin r × Payload I)) (hU : LocalOn I r A U) (hV : LocalOn I r A V) :
    LocalOn I r A (U*V) := by
  obtain ⟨u,hu,heu⟩ := hU
  obtain ⟨v,hv,hev⟩ := hV
  have hU' : U=localRegisterGate I r A u := by ext i j; exact heu i j
  have hV' : V=localRegisterGate I r A v := by ext i j; exact hev i j
  rw [hU',hV',← localRegisterGate_mul]
  exact localRegisterGate_local I r A (u*v) (unitary_mul hu hv)

def postcomposeTester {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (k : Cut S)
    (U : Mat (Fin r × Restricted I (held S k)ᶜ)) (hU : IsUnitary U) : Tester S r where
  initial := t.initial
  normalized := t.normalized
  gate l := if l=k then localRegisterGate I r (held S k)ᶜ U * t.gate l else t.gate l
  unitary l := by
    split_ifs with h
    · subst l
      exact unitary_mul (localRegisterGate_unitary I r _ U hU) (t.unitary k)
    · exact t.unitary l
  gate_local l := by
    split_ifs with h
    · subst l
      exact localOn_mul I r _ _ _ (localRegisterGate_local I r _ U hU) (t.gate_local k)
    · exact t.gate_local l

theorem postcomposeTester_initial {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (k : Cut S)
    (U : Mat (Fin r × Restricted I (held S k)ᶜ)) (hU : IsUnitary U) :
    (postcomposeTester t k U hU).initial=t.initial := rfl

theorem postcomposeTester_gate_ne {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (k l : Cut S)
    (U : Mat (Fin r × Restricted I (held S k)ᶜ)) (hU : IsUnitary U) (hl : l ≠ k) :
    (postcomposeTester t k U hU).gate l=t.gate l := by
  simp only [postcomposeTester, if_neg hl]

theorem jointGate_congr {I : Inventory} {S : Schedule I} {r : ℕ}
    (e : Extension S) (t u : Tester S r) (k : Cut S) (h : t.gate k=u.gate k) :
    jointGate e t k=jointGate e u k := by
  rw [jointGate_as_product, jointGate_as_product, h]

theorem run_tester_prefix_congr {I : Inventory} {S : Schedule I} {r : ℕ}
    (e : Extension S) (t u : Tester S r) (h0 : t.initial=u.initial)
    (n : ℕ) (hg : ∀ k : Cut S, k.val<n → t.gate k=u.gate k) : run e t n=run e u n := by
  revert hg
  induction n with
  | zero => intro _; simp only [run, initialState, h0]
  | succ n ih =>
      intro hg
      have hi := ih (fun k hk => hg k (Nat.lt_succ_of_lt hk))
      simp only [run]
      split_ifs with hn
      · rw [hi,jointGate_congr e t u ⟨n,hn⟩ (hg _ (Nat.lt_succ_self n))]
      · exact hi

theorem postcomposeTester_run_before {I : Inventory} {S : Schedule I} {r : ℕ}
    (e : Extension S) (t : Tester S r) (k : Cut S)
    (U : Mat (Fin r × Restricted I (held S k)ᶜ)) (hU : IsUnitary U)
    (n : ℕ) (hn : n ≤ k.val) : run e (postcomposeTester t k U hU) n=run e t n := by
  apply run_tester_prefix_congr e (postcomposeTester t k U hU) t rfl n
  intro l hl
  apply postcomposeTester_gate_ne
  intro he
  have hv := congrArg Fin.val he
  omega

theorem liftTesterObservable_mul {I : Inventory} {S : Schedule I}
    (e : Extension S) (r : ℕ) (U V : Mat (Fin r × Payload I)) :
    liftTesterObservable e r (U*V) = liftTesterObservable e r U * liftTesterObservable e r V := by
  unfold liftTesterObservable
  rw [← mul_kronecker_mul, one_mul, submatrix_mul_equiv]

theorem postcomposeTester_run_after {I : Inventory} {S : Schedule I} {r : ℕ}
    (e : Extension S) (t : Tester S r) (k : Cut S)
    (U : Mat (Fin r × Restricted I (held S k)ᶜ)) (hU : IsUnitary U) :
    run e (postcomposeTester t k U hU) (k.val+1) =
      evolve (liftTesterObservable e r (localRegisterGate I r (held S k)ᶜ U))
        (run e t (k.val+1)) := by
  have hj : jointGate e (postcomposeTester t k U hU) k =
      liftTesterObservable e r (localRegisterGate I r (held S k)ᶜ U) * jointGate e t k := by
    rw [jointGate_as_product, jointGate_as_product]
    have hgate : (postcomposeTester t k U hU).gate k =
        localRegisterGate I r (held S k)ᶜ U * t.gate k := by
      simp [postcomposeTester]
    rw [hgate,liftTesterObservable_mul,mul_assoc]
  rw [run, dif_pos k.isLt, postcomposeTester_run_before e t k U hU k.val le_rfl]
  change evolve (jointGate e (postcomposeTester t k U hU) k) (run e t k.val) = _
  rw [hj,evolve_mul]
  rw [run,dif_pos k.isLt]

theorem postcomposeTester_prefixGram {I : Inventory} {S : Schedule I} {r : ℕ}
    (t : Tester S r) (k : Cut S)
    (U : Mat (Fin r × Restricted I (held S k)ᶜ)) (hU : IsUnitary U)
    (b : InputBurst S) (hb : recordTime b ≤ k.val) :
    prefixGram b (postcomposeTester t k U hU)=prefixGram b t := by
  unfold prefixGram
  rw [gram_physical,gram_physical]
  unfold chi
  rw [postcomposeTester_run_before _ t k U hU (recordTime b) hb]

/-- Equal inaccessible marginals of two pure vectors are related by a full
square unitary on the accessible factor, including all reference correlations. -/
theorem pure_marginal_square_unitary {a z : Type} [Fintype a] [DecidableEq a]
    [Fintype z] [DecidableEq z] (ψ φ : a × z → ℂ)
    (h : partialRight (pureMatrix ψ)=partialRight (pureMatrix φ)) :
    ∃ U : Mat z, IsUnitary U ∧ ∀ x y, φ (x,y)=∑ w,ψ (x,w)*U y w := by
  let A : Matrix a z ℂ := fun x y => ψ (x,y)
  let B : Matrix a z ℂ := fun x y => φ (x,y)
  have hg : A*Aᴴ=B*Bᴴ := by ext i j; exact congrFun₂ h i j
  obtain ⟨U,hU,hfactor⟩ := gram_factor_isometry A B hg le_rfl
  exact ⟨U,⟨hU,mul_eq_one_comm.mp hU⟩,fun x y => congrFun₂ hfactor x y⟩

theorem pure_marginal_unitary_preparation {a z : Type} [Fintype a] [DecidableEq a]
    [Fintype z] [DecidableEq z] (ψ φ : a × z → ℂ)
    (h : partialRight (pureMatrix ψ)=partialRight (pureMatrix φ)) :
    ∃ U : Mat z, IsUnitary U ∧ evolve ((1 : Mat a) ⊗ₖ U) (pureMatrix ψ)=pureMatrix φ := by
  obtain ⟨U,hU,hfactor⟩ := pure_marginal_square_unitary ψ φ h
  refine ⟨U,hU,?_⟩
  have hv : ((1 : Mat a) ⊗ₖ U)*ᵥψ=φ := by
    funext x
    simpa [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,kroneckerMap_apply,
      Matrix.one_apply,ite_mul,Finset.sum_ite_irrel,mul_comm] using (hfactor x.1 x.2).symm
  rw [evolve,← pureMatrix_mulVec,hv]

end ScheduleLaw.Blueprint
