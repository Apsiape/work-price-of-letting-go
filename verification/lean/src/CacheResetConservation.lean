import CachePhysicalHamiltonian

set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.CachePhysicalHamiltonian
open History CacheHardware
variable {d n : ℕ} {β : ℝ} {τ q : Density (Fin d)}

theorem unframe {a b : Type} (E : a ≃ b) (A : Mat a) (B : Mat b)
    (h : A.submatrix E.symm E.symm = B) : A = B.submatrix E E := by
  have hh := congrArg (fun M : Mat b => M.submatrix E E) h
  simpa only [submatrix_submatrix,Equiv.symm_comp_self,submatrix_id_id] using hh

def resetFrame (F : Formation β τ q (n+1)) := (bodyFrame F).trans (activeFrame F)

theorem packed_resetFrame (F : Formation β τ q (n+1)) (service : ℝ) :
    packed F service=(CacheTerminalReset.hamiltonian (tangentHamiltonian β q) (active F service)).submatrix
      (resetFrame F) (resetFrame F) := unframe _ _ _ (active_packed F service)

theorem reset_resetFrame (F : Formation β τ q (n+1)) :
    reset F = ((FactoryReset.swap (a:=Fin d) (b:=ActiveRest F)).permMatrix ℂ).submatrix
      (resetFrame F) (resetFrame F) := by
  rfl

theorem terminal_transport {a b c : Type} [Fintype a] [Fintype b] [Fintype c]
    [da : DecidableEq a] [db : DecidableEq b] [DecidableEq c]
    (D : DecidableEq (a × (b × a))) (E : c ≃ a × (b × a)) (H : Mat a) (K : Mat b) :
    Conserves ((@Equiv.Perm.permMatrix (a × (b × a)) ℂ D
      (FactoryReset.swap (a:=a) (b:=b)) _ _).submatrix E E)
      ((CacheTerminalReset.hamiltonian H K).submatrix E E) := by
  have hh : D = (fun i j => @instDecidableEqProd a (b × a) da
      (fun i j => @instDecidableEqProd b a db da i j) i j) := Subsingleton.elim _ _
  rw [hh]
  exact CacheTerminalReset.reindexed_conserving E H K

theorem reset_conserves (F : Formation β τ q (n+1)) (service : ℝ) :
    Conserves (reset F) (packed F service) := by
  rw [reset_resetFrame,packed_resetFrame]
  exact terminal_transport _ (resetFrame F) (tangentHamiltonian β q) (active F service)

end ScheduleLaw.Blueprint.CachePhysicalHamiltonian
