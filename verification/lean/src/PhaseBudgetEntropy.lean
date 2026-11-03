import PhaseHardwareComparison
import PhaseEntropyRefund
import FactoryDrivenBudgets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 250000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseBudgetEntropy
open History
variable {I : Inventory} {S : Schedule I} {β : ℝ}

def controllerDensity (p : Driven S β) {z : ℕ} (t : Tester S z) : Density (Fin p.c) := by
  have h := bodyOutput_density p.extension t
  exact ⟨Driven.controllerFinal p t,partialRight_positive (h.1.submatrix p.split.symm),by
    unfold Driven.controllerFinal
    rw [partialRight_trace,submatrix_trace_equiv,h.2]⟩

def product {a b : Type} [Fintype a] [Fintype b] (ρ : Density a) (φ : Density b) : Density (a × b) :=
  ⟨ρ.matrix ⊗ₖ φ.matrix,ρ.positive.kronecker φ.positive,by
    rw [trace_kronecker,ρ.normalized,φ.normalized,mul_one]⟩

def reindex {a b : Type} [Fintype a] [Fintype b] (e : a ≃ b) (ρ : Density b) : Density a :=
  ⟨ρ.matrix.submatrix e e,ρ.positive.submatrix _,by rw [submatrix_trace_equiv]; exact ρ.normalized⟩

theorem product_entropy {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ρ : Density a) (φ : Density b) : entropy (product ρ φ).matrix=entropy ρ.matrix+entropy φ.matrix :=
  entropy_density_product ρ φ

theorem reindex_entropy {a b : Type} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : a ≃ b) (ρ : Density b) : entropy (reindex e ρ).matrix=entropy ρ.matrix :=
  entropy_submatrix_equiv e ρ.matrix ρ.positive.isHermitian

variable (p : Driven S β) {D : ℕ} (hD : 0<D) (φ : Density (Fin D)) (Hφ : Hamiltonian (Fin D))
    (G : Cut S → Mat (Fin (p.extension.b*D) × Payload I))
    (hG : ∀ k,IsUnitary (G k)) (hlocal : ∀ k,LocalOn I (p.extension.b*D) (held S k) (G k))
local notation "q" => PhaseHardware.hardware p hD φ Hφ G hG hlocal

theorem controller (rank L : ℕ) (K η : ℝ) (hdim : D=(L+4)^rank)
    (hclose : PhaseHardwareComparison.Close p hD φ Hφ G hG hlocal (K/(L+1 : ℝ)))
    {z : ℕ} (t : Tester S z) (hold : |Driven.controllerEntropyChange p t|≤η) :
    |Driven.controllerEntropyChange q t|≤η+PhaseEntropyLimit.modulus p.c rank K L := by
  letI dc : DecidableEq (Fin p.c) := inferInstance
  letI df : DecidableEq (Fin D) := inferInstance
  letI : DecidableEq (Fin p.c × Fin D) := @instDecidableEqProd _ _ dc df
  let ρ := controllerDensity q t
  let σ := reindex (finProdFinEquiv.symm : Fin (p.c*D) ≃ Fin p.c × Fin D)
    (product (controllerDensity p t) φ)
  have hσ : entropy σ.matrix=entropy (Driven.controllerFinal p t)+entropy φ.matrix := by
    rw [reindex_entropy,product_entropy]
    rfl
  have hsource : entropy (q).controller.matrix=entropy p.controller.matrix+entropy φ.matrix := by
    change entropy (reindex (finProdFinEquiv.symm : Fin (p.c*D) ≃ Fin p.c × Fin D)
      (product p.controller φ)).matrix=_
    rw [reindex_entropy,product_entropy]
  have hacc : traceDistance ρ.matrix σ.matrix≤K/(L+1 : ℝ) :=
    PhaseHardwareComparison.controller p hD φ Hφ G hG hlocal _ hclose t
  have hcard : Fintype.card (Fin (p.c*D))=p.c*(L+4)^rank := by simp [hdim]
  have hs := PhaseEntropyRefund.bound ρ σ p.c rank L p.c_pos K hcard hacc
  have he : Driven.controllerEntropyChange q t=
      (entropy ρ.matrix-entropy σ.matrix)+Driven.controllerEntropyChange p t := by
    unfold Driven.controllerEntropyChange
    rw [hsource,hσ]
    change entropy ρ.matrix-(entropy p.controller.matrix+entropy φ.matrix)=_
    ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

theorem battery (L : ℕ) (K η : ℝ)
    (hclose : PhaseHardwareComparison.Close p hD φ Hφ G hG hlocal (K/(L+1 : ℝ)))
    {z : ℕ} (t : Tester S z) (hold : entropy (Driven.batteryFinal p t)≤η) :
    entropy (Driven.batteryFinal q t)≤η+PhaseEntropyLimit.modulus p.w 0 K L := by
  let ρ := FactoryDrivenBudgets.batteryDensity q t
  let σ := FactoryDrivenBudgets.batteryDensity p t
  have hacc : traceDistance ρ.matrix σ.matrix≤K/(L+1 : ℝ) :=
    PhaseHardwareComparison.battery p hD φ Hφ G hG hlocal _ hclose t
  have hc : Fintype.card (Fin p.w)=p.w*(L+4)^0 := by simp
  have hs := PhaseEntropyRefund.bound ρ σ p.w 0 L p.w_pos K hc hacc
  have hh := (abs_le.mp hs).2
  change entropy (Driven.batteryFinal q t)-entropy (Driven.batteryFinal p t)≤_ at hh
  linarith

end ScheduleLaw.Blueprint.PhaseBudgetEntropy
