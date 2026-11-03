import PhaseGateColumn
import PhaseReferenceBound

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace ScheduleLaw.Blueprint.PhaseGateAccuracy
open PhaseVectorDistance PhaseLatticeBox PhasePacketDensity PhaseShiftPacket PhaseGateColumn
variable {s ι : Type} [Fintype s] [DecidableEq s] [Fintype ι] [DecidableEq ι]

theorem unitary_column_square (U : Mat s) (hU : IsUnitary U) (j : s) :
    (∑ i,‖U i j‖^2)=1 := by
  let e : s → ℂ := fun i => if i=j then 1 else 0
  have hn : ‖vector e‖=1 := by simp [EuclideanSpace.norm_eq,vector,e,apply_ite]
  have he : U *ᵥ e=(fun i => U i j) := by
    ext i
    simp [Matrix.mulVec,dotProduct,e,mul_ite]
  have hu := norm_unitary U hU e
  rw [he,hn] at hu
  have hs := EuclideanSpace.norm_sq_eq (vector (fun i => U i j))
  rw [hu,one_pow] at hs
  exact hs.symm

def errorColumn (a : s → PhaseLatticeBox.Lattice ι) (L : ℕ) (U : Mat s) (j : s) :
    FinitePhaseShell.State (ι:=s) (box ι L) → ℂ :=
  fun x => column a L U j x-U x.1 j*packet L x.2

theorem column_error (a : s → PhaseLatticeBox.Lattice ι) (ha : ∀ j k,0≤a j k ∧ a j k≤1)
    (L : ℕ) (hL : 0<L) (U : Mat s) (hU : IsUnitary U) (j : s) :
    ‖vector (errorColumn a L U j)‖≤((Fintype.card ι : ℝ)+1)*Real.pi/(L+1 : ℝ) := by
  let ε := ((Fintype.card ι : ℝ)+1)*Real.pi/(L+1 : ℝ)
  have hε : 0≤ε := by dsimp only [ε]; positivity
  let f (i : s) (x : ↥(box ι L)) := raw L (x.val+a i-a j)-packet L x
  have hf (i : s) : ‖vector (f i)‖≤ε := by
    have hd (k : ι) : -1≤(a j-a i) k ∧ (a j-a i) k≤1 := by
      have h1 := ha j k
      have h2 := ha i k
      change -1≤a j k-a i k ∧ a j k-a i k≤1
      omega
    have h := translated_difference L hL (a j-a i) hd
    have he : f i=(fun x : ↥(box ι L) => raw L (x.val-(a j-a i))-packet L x) := by
      funext x
      dsimp only [f]
      congr 2
      abel
    rw [he]
    exact h
  have hc (i : s) (x : ↥(box ι L)) : errorColumn a L U j (i,x)=U i j*f i x := by
    rw [errorColumn,column_formula a ha]
    dsimp only [f]
    ring
  have hs : ‖vector (errorColumn a L U j)‖^2≤ε^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [vector,PiLp.toLp_apply,Fintype.sum_prod_type,hc,norm_mul,mul_pow]
    calc _ = ∑ i,‖U i j‖^2*‖vector (f i)‖^2 := by
           apply Finset.sum_congr rfl
           intro i _
           rw [EuclideanSpace.norm_sq_eq,Finset.mul_sum]
         _ ≤ ∑ i,‖U i j‖^2*ε^2 := Finset.sum_le_sum (fun i _ =>
           mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hf i) 2) (sq_nonneg _))
         _ = ε^2 := by rw [← Finset.sum_mul,unitary_column_square U hU j,one_mul]
  nlinarith [norm_nonneg (vector (errorColumn a L U j))]

def errorMatrix (a : s → PhaseLatticeBox.Lattice ι) (L : ℕ) (U : Mat s) :
    Matrix (FinitePhaseShell.State (ι:=s) (box ι L)) s ℂ := fun x j => errorColumn a L U j x

theorem arbitrary_reference {r : Type} [Fintype r]
    (a : s → PhaseLatticeBox.Lattice ι) (ha : ∀ j k,0≤a j k ∧ a j k≤1)
    (L : ℕ) (hL : 0<L) (U : Mat s) (hU : IsUnitary U) (hs : 0<Fintype.card s)
    (ψ : Matrix s r ℂ) (hψ : ‖vector (fun x : s × r => ψ x.1 x.2)‖=1) :
    ‖vector (fun x : (FinitePhaseShell.State (ι:=s) (box ι L)) × r =>
      (errorMatrix a L U*ψ) x.1 x.2)‖≤
        (Fintype.card s : ℝ)*(((Fintype.card ι : ℝ)+1)*Real.pi/(L+1 : ℝ)) := by
  apply PhaseReferenceBound.uniform_reference _ ψ _ (by positivity) hs
  · intro j
    exact column_error a ha L hL U hU j
  · exact hψ

end ScheduleLaw.Blueprint.PhaseGateAccuracy
