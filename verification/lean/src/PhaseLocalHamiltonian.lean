import FactoryGibbsReindex
import FactoryGibbsProduct
import BlueprintContracts
import OwnedEnergy

set_option autoImplicit false
set_option maxHeartbeats 300000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseLocalHamiltonian
open History
variable {I : Inventory} {S : Schedule I} {β : ℝ}

/-- Exactly the original complete body Hamiltonian, packaged with its
Hermiticity proof for the local spectral construction. -/
def body (p : Driven S β) : Hamiltonian (Fin p.extension.b) :=
  FactoryGibbs.reindexHamiltonian p.split
    (FactoryGibbs.sumHamiltonian p.HC (FactoryGibbs.sumHamiltonian
      (FlatMatrix.diagonalHamiltonian (Fin p.w) p.batteryEnergy) p.HR))

theorem body_matrix (p : Driven S β) : (body p).matrix=p.bodyHamiltonian := rfl

def component (I : Inventory) (A : Finset (Fin I.count)) (c : {c // c∈A}) :
    Mat (Restricted I A) := fun u v =>
  (I.H c.val).matrix (u c) (v c)*
    (if ∀ j : {j // j∈A},j.val≠c.val → u j=v j then 1 else 0)

theorem component_hermitian (I : Inventory) (A : Finset (Fin I.count)) (c : {c // c∈A}) :
    (component I A c).IsHermitian := by
  change (component I A c)ᴴ=component I A c
  ext u v
  have hH : star ((I.H c.val).matrix (v c) (u c))=(I.H c.val).matrix (u c) (v c) := by
    exact congrFun (congrFun (I.H c.val).hermitian.eq (u c)) (v c)
  change star ((I.H c.val).matrix (v c) (u c)*
      (if ∀ j : {j // j∈A},j.val≠c.val → v j=u j then 1 else 0))=
    (I.H c.val).matrix (u c) (v c)*
      (if ∀ j : {j // j∈A},j.val≠c.val → u j=v j then 1 else 0)
  by_cases hh : ∀ j : {j // j∈A},j.val≠c.val → u j=v j
  · have hr : ∀ j : {j // j∈A},j.val≠c.val → v j=u j := fun j hj => (hh j hj).symm
    rw [if_pos hh,if_pos hr,mul_one,mul_one]
    exact hH
  · have hr : ¬∀ j : {j // j∈A},j.val≠c.val → v j=u j := by
      intro h
      exact hh (fun j hj => (h j hj).symm)
    rw [if_neg hh,if_neg hr,mul_zero,mul_zero,star_zero]

/-- The Hamiltonian on precisely the listed physical carriers. -/
def restricted (I : Inventory) (A : Finset (Fin I.count)) : Hamiltonian (Restricted I A) where
  matrix := ∑ c : {c // c∈A},component I A c
  hermitian := by
    change (∑ c : {c // c∈A},component I A c)ᴴ=∑ c : {c // c∈A},component I A c
    rw [conjTranspose_sum]
    exact Finset.sum_congr rfl (fun c _ => (component_hermitian I A c).eq)

def localH (p : Driven S β) (A : Finset (Fin I.count)) : Hamiltonian (Fin p.extension.b × Restricted I A) :=
  FactoryGibbs.sumHamiltonian (body p) (restricted I A)

theorem local_matrix (p : Driven S β) (A : Finset (Fin I.count)) :
    (localH p A).matrix=p.bodyHamiltonian ⊗ₖ (1 : Mat (Restricted I A))+
      (1 : Mat (Fin p.extension.b)) ⊗ₖ (restricted I A).matrix := rfl

theorem owned_component (I : Inventory) (b : ℕ) (A : Finset (Fin I.count)) (c : {c // c∈A}) :
    ownedCarrier I b A c.val c.property=(1 : Mat (Fin b)) ⊗ₖ component I A c := by
  ext i j
  simp only [ownedCarrier,component,kroneckerMap_apply,Matrix.one_apply]
  by_cases hb : i.1=j.1 <;>
    by_cases hr : ∀ k : {k // k∈A},k.val≠c.val → i.2 k=j.2 k <;>
      simp [hb,hr]

end ScheduleLaw.Blueprint.PhaseLocalHamiltonian
