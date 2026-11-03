import CacheServiceGates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CachePreparationHistory
open History
variable {I : Inventory} {S : Schedule I}

theorem joint_first (e : Extension S) (U : Mat (Fin e.b)) (hU : IsUnitary U)
    {z : ℕ} (t : Tester S z) :
    jointGate (CacheServiceGates.prepare e U hU) t ⟨0,by omega⟩ =
      jointGate e t ⟨0,by omega⟩ * (U ⊗ₖ (1 : Mat (Payload I × Fin z))) := by
  rw [jointGate_as_product,jointGate_as_product]
  change liftTesterObservable e z (t.gate ⟨0,by omega⟩) *
    liftDeviceObservable e z (e.gate ⟨0,by omega⟩ * (U ⊗ₖ 1)) = _
  have hm (A B : Mat (Fin e.b × Payload I)) :
      liftDeviceObservable e z (A*B) = liftDeviceObservable e z A * liftDeviceObservable e z B := by
    unfold liftDeviceObservable
    rw [submatrix_mul_equiv,← mul_kronecker_mul,one_mul]
  rw [hm,liftDevice_body,mul_assoc]

theorem history (e : Extension S) (U : Mat (Fin e.b)) (hU : IsUnitary U)
    {z : ℕ} (t : Tester S z) (n : ℕ) (hn : 0<n) :
    historyUnitary (CacheServiceGates.prepare e U hU) t n =
      historyUnitary e t n * (U ⊗ₖ (1 : Mat (Payload I × Fin z))) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero =>
      simp only [historyUnitary,dif_pos (show 0<2*S.visits+1 by omega),mul_one]
      exact joint_first e U hU t
    | succ n =>
      by_cases h : n+1<2*S.visits+1
      · rw [show historyUnitary (CacheServiceGates.prepare e U hU) t (n+1+1) =
          jointGate (CacheServiceGates.prepare e U hU) t ⟨n+1,h⟩ *
            historyUnitary (CacheServiceGates.prepare e U hU) t (n+1) from dif_pos h,
          show historyUnitary e t (n+1+1) =
            jointGate e t ⟨n+1,h⟩ * historyUnitary e t (n+1) from dif_pos h,ih (by omega)]
        have hj : jointGate (CacheServiceGates.prepare e U hU) t ⟨n+1,h⟩ =
            jointGate e t ⟨n+1,h⟩ := by
          simp only [jointGate,CacheServiceGates.prepare,if_neg (show n+1≠0 by omega)]
        rw [hj,mul_assoc]
      · rw [show historyUnitary (CacheServiceGates.prepare e U hU) t (n+1+1) =
          historyUnitary (CacheServiceGates.prepare e U hU) t (n+1) from dif_neg h,
          show historyUnitary e t (n+1+1) = historyUnitary e t (n+1) from dif_neg h,
          ih (by omega)]

theorem run (e : Extension S) (U : Mat (Fin e.b)) (hU : IsUnitary U)
    {z : ℕ} (t : Tester S z) (n : ℕ) (hn : 0<n) :
    ScheduleLaw.run (CacheServiceGates.prepare e U hU) t n =
      evolve (historyUnitary e t n) (evolve U e.source.matrix ⊗ₖ initialTesterMatrix t) := by
  rw [run_eq_history,history e U hU t n hn,evolve_mul]
  change evolve (historyUnitary e t n)
    (evolve (U ⊗ₖ (1 : Mat (Payload I × Fin z)))
      (e.source.matrix ⊗ₖ initialTesterMatrix t)) = _
  rw [IdleExtension.evolve_idle]

/-- The source obtained after the one initial square preparation. -/
def preparedSource (e : Extension S) (U : Mat (Fin e.b)) (hU : IsUnitary U) :
    Density (Fin e.b) :=
  ⟨evolve U e.source.matrix,(evolve_density U e.source.matrix hU e.source.positive e.source.normalized).1,
    (evolve_density U e.source.matrix hU e.source.positive e.source.normalized).2⟩

theorem run_source (e : Extension S) (U : Mat (Fin e.b)) (hU : IsUnitary U)
    {z : ℕ} (t : Tester S z) (n : ℕ) (hn : 0<n) :
    ScheduleLaw.run (CacheServiceGates.prepare e U hU) t n =
      ScheduleLaw.run (CacheSourceHistory.withSource e (preparedSource e U hU)) t n := by
  rw [run e U hU t n hn,CacheSourceHistory.run]
  rfl

theorem observer_output (e : Extension S) (U : Mat (Fin e.b)) (hU : IsUnitary U)
    {z : ℕ} (t : Tester S z) :
    observerOutput (CacheServiceGates.prepare e U hU) t =
      observerOutput (CacheSourceHistory.withSource e (preparedSource e U hU)) t := by
  unfold observerOutput finalState
  rw [run_source e U hU t _ (by omega)]

theorem body_output (e : Extension S) (U : Mat (Fin e.b)) (hU : IsUnitary U)
    {z : ℕ} (t : Tester S z) :
    bodyOutput (CacheServiceGates.prepare e U hU) t =
      bodyOutput (CacheSourceHistory.withSource e (preparedSource e U hU)) t := by
  unfold bodyOutput finalState
  rw [run_source e U hU t _ (by omega)]

theorem handoff (e : Extension S) (U : Mat (Fin e.b)) (hU : IsUnitary U)
    {z : ℕ} (t : Tester S z) :
    ScheduleLaw.handoff (CacheServiceGates.prepare e U hU) t =
      ScheduleLaw.handoff (CacheSourceHistory.withSource e (preparedSource e U hU)) t := by
  unfold ScheduleLaw.handoff
  apply Finset.sum_congr rfl
  intro v _
  unfold carrierEnergy
  rw [run_source e U hU t _ (by omega),run_source e U hU t _ (by omega)]
  rfl

end ScheduleLaw.Blueprint.CachePreparationHistory
