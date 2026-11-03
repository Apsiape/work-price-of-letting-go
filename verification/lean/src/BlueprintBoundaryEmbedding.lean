import BlueprintBurstExecution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History

def frameEmbedding {a m z b : Type} (C : b ≃ a × z) (e : m ↪ z) : (a × m) ↪ b where
  toFun q := C.symm (q.1,e q.2)
  inj' := by
    intro q r h
    have he := C.symm.injective h
    have hx : q.1=r.1 := congrArg (fun p : a × z => p.1) he
    have hm : q.2=r.2 := e.injective (congrArg (fun p : a × z => p.2) he)
    exact Prod.ext hx hm

theorem frameEmbedding_vector {a m z b : Type} [Fintype a] [Fintype m]
    [DecidableEq b] [DecidableEq z] (C : b ≃ a × z) (e : m ↪ z)
    (P : a × m → ℂ) (x : b) :
    (registerEmbedding (frameEmbedding C e)*ᵥP) x=
      ∑ q, P ((C x).1,q)*registerEmbedding e (C x).2 q := by
  classical
  have he (u : a) (q : m) : x=C.symm (u,e q) ↔ (C x).1=u ∧ (C x).2=e q := by
    rw [Equiv.eq_symm_apply,Prod.mk.injEq]
  simp only [Matrix.mulVec,dotProduct,registerEmbedding,frameEmbedding,Fintype.sum_prod_type]
  change (∑ u : a,∑ q : m,(if x=C.symm (u,e q) then (1:ℂ) else 0)*P (u,q))=
    ∑ q : m,P ((C x).1,q)*(if (C x).2=e q then (1:ℂ) else 0)
  simp_rw [he]
  rw [Finset.sum_comm]
  simp [ite_mul,mul_ite,ite_and]

def canonicalRawEmbedding {I : Inventory} {S : Schedule I} (b : InputBurst S) :
    (PrefixSpace b × (PrefixSpace b × Registers S (released S (recordTime b))ᶜ)) ↪
      Raw S (burstMemoryDim S) :=
  frameEmbedding (recordCoordinates S _ _ _) (canonicalEnvironmentEmbedding b)

theorem canonicalPrefixVector_embedding {I : Inventory} {S : Schedule I}
    (Z : PrefixMatrices S) (hZ : IsCausalPrefixFamily S Z) (b : InputBurst S) :
    (registerEmbedding (canonicalRawEmbedding b)*ᵥ
      (fun q => prefixPurification S Z hZ b (q.1,q.2.1)))=canonicalPrefixVector Z hZ b := by
  funext x
  rw [canonicalRawEmbedding,frameEmbedding_vector]
  rfl

def bellProductEmbedding {I : Inventory} {S : Schedule I} {r : ℕ} {a : Type}
    (e : a ↪ (Fin r × Payload I)) : (a × Recorder.Inputs S) ↪ Raw S r where
  toFun q := ((q.2,q.2),((e q.1).2,(e q.1).1))
  inj' := by
    intro q s h
    have he : e q.1=e s.1 := Prod.ext (congrArg (fun y => y.2.2) h) (congrArg (fun y => y.2.1) h)
    exact Prod.ext (e.injective he) (congrArg (fun y => y.1.1) h)

theorem bellProductEmbedding_vector {I : Inventory} {S : Schedule I} {r : ℕ}
    {a : Type} [Fintype a] (e : a ↪ (Fin r × Payload I)) (v : a → ℂ) (x : Raw S r) :
    (registerEmbedding (bellProductEmbedding (S := S) e)*ᵥ(fun q => v q.1)) x=
      allBellSource S x.1*(registerEmbedding e*ᵥv) (x.2.2,x.2.1) := by
  classical
  rcases x with ⟨⟨ain,partner⟩,p,m⟩
  simp only [Matrix.mulVec,dotProduct,registerEmbedding,bellProductEmbedding,Fintype.sum_prod_type]
  by_cases hx : ain=partner
  · simp [Prod.mk.injEq,hx,allBellSource,ite_and,ite_mul]
    apply Finset.sum_congr rfl
    intro q _
    by_cases hp : p=(e q).2 <;> by_cases hm : m=(e q).1 <;>
      simp [hp,hm,Prod.ext_iff]
  · have hh (u : Recorder.Inputs S) : ¬(ain=u ∧ partner=u) := by
      rintro ⟨h1,h2⟩
      exact hx (h1.trans h2.symm)
    simp [Prod.mk.injEq,hh,allBellSource,hx,and_assoc]

theorem embedded_vector_transport {a b z : Type} [Fintype a] [Fintype b] [DecidableEq z]
    (e : a ↪ z) (f : b ↪ z) (E : a ≃ b) (σ : Equiv.Perm z)
    (he : ∀ q, σ (e q)=f (E q)) (v : a → ℂ) (w : b → ℂ)
    (hv : ∀ q, v q=w (E q)) (x : z) :
    (registerEmbedding e*ᵥv) (σ.symm x)=(registerEmbedding f*ᵥw) x := by
  have hcond (q : a) : σ.symm x=e q ↔ x=f (E q) := by
    rw [Equiv.symm_apply_eq,he]
  simp only [Matrix.mulVec,dotProduct,registerEmbedding,hcond,hv]
  exact E.sum_comp (fun q => (if x=f q then (1:ℂ) else 0)*w q)

end ScheduleLaw.Blueprint
