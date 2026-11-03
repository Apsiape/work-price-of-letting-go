import BlueprintTesterCut

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

/-- The inaccessible factor is the device and the complementary physical
carriers; the accessible factor is the fixed tester memory and allowed carriers. -/
def testerLocalCoordinates {a : Type} (I : Inventory) (r : ℕ) (A : Finset (Fin I.count)) :
    (a × (Payload I × Fin r)) ≃ (a × Restricted I Aᶜ) × (Fin r × Restricted I A) where
  toFun x := ((x.1,restrictPayload I Aᶜ x.2.1),(x.2.2,restrictPayload I A x.2.1))
  invFun x := (x.1.1,((payloadPartition I A).symm (x.2.2,x.1.2),x.2.1))
  left_inv x := by
    change (x.1,((payloadPartition I A).symm ((payloadPartition I A) x.2.1),x.2.2))=x
    rw [Equiv.symm_apply_apply]
  right_inv x := by
    have h := (payloadPartition I A).apply_symm_apply (x.2.2,x.1.2)
    have hA : restrictPayload I A ((payloadPartition I A).symm (x.2.2,x.1.2))=x.2.2 :=
      congrArg Prod.fst h
    have hC : restrictPayload I Aᶜ ((payloadPartition I A).symm (x.2.2,x.1.2))=x.1.2 :=
      congrArg Prod.snd h
    change ((x.1.1,restrictPayload I Aᶜ ((payloadPartition I A).symm (x.2.2,x.1.2))),
      (x.2.1,restrictPayload I A ((payloadPartition I A).symm (x.2.2,x.1.2))))=x
    rw [hA,hC]

theorem liftTesterLocalGate_coordinates {I : Inventory} {S : Schedule I}
    (e : Extension S) (r : ℕ) (A : Finset (Fin I.count))
    (U : Mat (Fin r × Restricted I A)) :
    liftTesterObservable e r (localRegisterGate I r A U) =
      ((1 : Mat (Fin e.b × Restricted I Aᶜ)) ⊗ₖ U).submatrix
        (testerLocalCoordinates I r A) (testerLocalCoordinates I r A) := by
  ext i j
  change (if i.1=j.1 then (1 : ℂ) else 0) *
    (U (i.2.2,restrictPayload I A i.2.1) (j.2.2,restrictPayload I A j.2.1) *
      (if restrictPayload I Aᶜ i.2.1=restrictPayload I Aᶜ j.2.1 then 1 else 0)) =
    (if (i.1,restrictPayload I Aᶜ i.2.1)=(j.1,restrictPayload I Aᶜ j.2.1) then 1 else 0) *
      U (i.2.2,restrictPayload I A i.2.1) (j.2.2,restrictPayload I A j.2.1)
  by_cases hb : i.1=j.1 <;>
    by_cases hc : restrictPayload I Aᶜ i.2.1=restrictPayload I Aᶜ j.2.1 <;>
    simp [hb,hc,Prod.mk.injEq]

/-- Exact preparation by a legal observer contact when the inaccessible
pure-state marginal is unchanged. No tester realization premise is used. -/
theorem local_pure_state_preparation {I : Inventory} {S : Schedule I}
    (e : Extension S) (r : ℕ) (A : Finset (Fin I.count))
    (ψ φ : Global e r → ℂ)
    (h : partialRight ((pureMatrix ψ).submatrix
        (testerLocalCoordinates I r A).symm (testerLocalCoordinates I r A).symm) =
      partialRight ((pureMatrix φ).submatrix
        (testerLocalCoordinates I r A).symm (testerLocalCoordinates I r A).symm)) :
    ∃ U : Mat (Fin r × Restricted I A), IsUnitary U ∧
      evolve (liftTesterObservable e r (localRegisterGate I r A U)) (pureMatrix ψ)=pureMatrix φ := by
  let C := testerLocalCoordinates (a := Fin e.b) I r A
  let ψ' := fun x => ψ (C.symm x)
  let φ' := fun x => φ (C.symm x)
  have hm : partialRight (pureMatrix ψ')=partialRight (pureMatrix φ') := h
  obtain ⟨U,hU,hprep⟩ := pure_marginal_unitary_preparation ψ' φ' hm
  refine ⟨U,hU,?_⟩
  have he := congrArg (fun M => M.submatrix C C) hprep
  change (evolve ((1 : Mat (Fin e.b × Restricted I Aᶜ)) ⊗ₖ U)
    (pureMatrix ψ')).submatrix C C=(pureMatrix φ').submatrix C C at he
  rw [← evolve_submatrix_equiv C] at he
  have hψ : (pureMatrix ψ').submatrix C C=pureMatrix ψ := by
    ext i j
    simp only [submatrix_apply,pureMatrix,ψ',Equiv.symm_apply_apply]
  have hφ : (pureMatrix φ').submatrix C C=pureMatrix φ := by
    ext i j
    simp only [submatrix_apply,pureMatrix,φ',Equiv.symm_apply_apply]
  rw [hψ,hφ] at he
  rw [liftTesterLocalGate_coordinates]
  exact he

/-- Insert the preparation in an actual Tester at one cut. Its initial state,
all other gates, all earlier run states and all earlier prefix Grams are retained. -/
theorem prepare_tester_at_cut {I : Inventory} {S : Schedule I} {r : ℕ}
    (e : Extension S) (t : Tester S r) (k : Cut S) (ψ φ : Global e r → ℂ)
    (hψ : run e t (k.val+1)=pureMatrix ψ)
    (h : partialRight ((pureMatrix ψ).submatrix
        (testerLocalCoordinates I r (held S k)ᶜ).symm
        (testerLocalCoordinates I r (held S k)ᶜ).symm) =
      partialRight ((pureMatrix φ).submatrix
        (testerLocalCoordinates I r (held S k)ᶜ).symm
        (testerLocalCoordinates I r (held S k)ᶜ).symm)) :
    ∃ u : Tester S r, u.initial=t.initial ∧
      (∀ l : Cut S, l ≠ k → u.gate l=t.gate l) ∧
      (∀ n : ℕ, n ≤ k.val → run e u n=run e t n) ∧
      (∀ b : InputBurst S, recordTime b ≤ k.val → prefixGram b u=prefixGram b t) ∧
      run e u (k.val+1)=pureMatrix φ := by
  obtain ⟨U,hU,hprep⟩ := local_pure_state_preparation e r (held S k)ᶜ ψ φ h
  refine ⟨postcomposeTester t k U hU,rfl,?_,?_,?_,?_⟩
  · intro l hl
    exact postcomposeTester_gate_ne t k l U hU hl
  · intro n hn
    exact postcomposeTester_run_before e t k U hU n hn
  · intro b hb
    exact postcomposeTester_prefixGram t k U hU b hb
  · rw [postcomposeTester_run_after,hψ]
    exact hprep

theorem recorder_run_pure {I : Inventory} (S : Schedule I) {r : ℕ}
    (t : Tester S r) (n : ℕ) :
    run (Recorder.extension S) t n = pureMatrix (fun x =>
      amplitudes t Recorder.epr n ((actual S r).symm x)) := by
  ext i j
  have h := congrFun₂ (run_amplitudes S t n) ((actual S r).symm i) ((actual S r).symm j)
  simpa only [submatrix_apply,Equiv.apply_symm_apply,pureMatrix] using h

end ScheduleLaw.Blueprint
