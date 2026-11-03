import CacheSourceHistory
import IdleExtension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CacheServiceGates
open History

variable {I : Inventory} {S : Schedule I} {a : Type} [Fintype a] [DecidableEq a]

/-- Place the bare service on its actual emitted cell; all other hardware
is retained, and may initially be correlated with that cell. -/
def wires {N b : ℕ} (e : Fin N ≃ Fin b × a) (p : Type) :
    Fin N × p ≃ (Fin b × p) × a where
  toFun z := (((e z.1).1,z.2),(e z.1).2)
  invFun z := (e.symm (z.1.1,z.2),z.1.2)
  left_inv z := by simp only [Prod.mk.eta,Equiv.symm_apply_apply]
  right_inv z := by rcases z with ⟨⟨i,p⟩,r⟩; simp only [Equiv.apply_symm_apply]

def gate (bare : Extension S) {N : ℕ} (e : Fin N ≃ Fin bare.b × a) (k : Cut S) :
    Mat (Fin N × Payload I) :=
  (bare.gate k ⊗ₖ (1 : Mat a)).submatrix (wires e _) (wires e _)

theorem unitary (bare : Extension S) {N : ℕ} (e : Fin N ≃ Fin bare.b × a) (k : Cut S) :
    IsUnitary (gate bare e k) :=
  unitary_submatrix _ (unitary_kron (bare.unitary k) (by constructor <;> simp))

theorem gate_local (bare : Extension S) {N : ℕ} (e : Fin N ≃ Fin bare.b × a) (k : Cut S) :
    LocalOn I N (held S k) (gate bare e k) := by
  obtain ⟨V,hV,hg⟩ := bare.gate_local k
  refine ⟨(V ⊗ₖ (1 : Mat a)).submatrix (wires e _) (wires e _),
    unitary_submatrix _ (unitary_kron hV (by constructor <;> simp)),?_⟩
  intro i j
  simp only [gate,wires,Equiv.coe_fn_mk,submatrix_apply,kroneckerMap_apply,hg,one_apply]
  ring

def extension (bare : Extension S) {N : ℕ} (hN : 0<N) (e : Fin N ≃ Fin bare.b × a)
    (ρ : Density (Fin N)) : Extension S where
  b := N
  b_pos := hN
  source := ρ
  f := N
  f_pos := hN
  purification := ρ.toMState.purify.vec
  purification_norm := by
    simpa only [Complex.normSq_eq_norm_sq,Ket.coe_fun_eq] using ρ.toMState.purify.normalized
  purification_reduces := density_purification_matrix ρ.toMState
  gate := gate bare e
  unitary := unitary bare e
  gate_local := gate_local bare e

/-- Apply the cache preparation exactly once, before the first bare gate.
The last-body reset can then use the existing finalBodyContact constructor. -/
def prepare (e : Extension S) (U : Mat (Fin e.b)) (hU : IsUnitary U) : Extension S where
  b := e.b
  b_pos := e.b_pos
  source := e.source
  f := e.f
  f_pos := e.f_pos
  purification := e.purification
  purification_norm := e.purification_norm
  purification_reduces := e.purification_reduces
  gate k := if k.val=0 then e.gate k*(U ⊗ₖ (1 : Mat (Payload I))) else e.gate k
  unitary k := by
    split_ifs
    · exact unitary_mul (e.unitary k) (unitary_kron hU (by constructor <;> simp))
    · exact e.unitary k
  gate_local k := by
    split_ifs
    · exact localOn_mul I e.b _ _ _ (e.gate_local k) (body_tensor_local I e.b _ U hU)
    · exact e.gate_local k

end ScheduleLaw.Blueprint.CacheServiceGates
