import PhaseHardware
import FactoryPhysicalHamiltonian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.PhaseHardwareEnergy
open History PhaseHardware
variable {I : Inventory} {S : Schedule I} {β : ℝ}

theorem physical (p : Driven S β) {D : ℕ} (hD : 0<D) (φ : Density (Fin D)) (Hφ : Hamiltonian (Fin D))
    (G : Cut S → Mat (Fin (p.extension.b*D) × Payload I))
    (hG : ∀ k,IsUnitary (G k)) (hlocal : ∀ k,LocalOn I (p.extension.b*D) (held S k) (G k)) :
    (hardware p hD φ Hφ G hG hlocal).bodyHamiltonian=
      (p.bodyHamiltonian ⊗ₖ (1 : Mat (Fin D))+(1 : Mat (Fin p.extension.b)) ⊗ₖ Hφ.matrix).submatrix
        finProdFinEquiv.symm finProdFinEquiv.symm := by
  change (((PhaseHardware.HC p Hφ).matrix ⊗ₖ (1 : Mat (Fin p.w × Fin p.r)))+
    (1 : Mat (Fin (p.c*D))) ⊗ₖ
      (Matrix.diagonal (fun j => (p.batteryEnergy j : ℂ)) ⊗ₖ (1 : Mat (Fin p.r))+
        (1 : Mat (Fin p.w)) ⊗ₖ p.HR.matrix)).submatrix
      (PhaseHardware.split p D) (PhaseHardware.split p D)=_
  ext i j
  obtain ⟨⟨b,z⟩,rfl⟩ := (finProdFinEquiv : Fin p.extension.b × Fin D ≃ Fin (p.extension.b*D)).surjective i
  obtain ⟨⟨b',z'⟩,rfl⟩ := (finProdFinEquiv : Fin p.extension.b × Fin D ≃ Fin (p.extension.b*D)).surjective j
  obtain ⟨⟨c,w,r⟩,rfl⟩ := p.split.symm.surjective b
  obtain ⟨⟨c',w',r'⟩,rfl⟩ := p.split.symm.surjective b'
  simp only [submatrix_apply,PhaseHardware.split_apply,Equiv.symm_apply_apply,
    Equiv.apply_symm_apply,PhaseHardware.HC,FactoryGibbs.reindexHamiltonian,
    FactoryGibbs.sumHamiltonian,Driven.bodyHamiltonian,kroneckerMap_apply,Matrix.add_apply]
  simp only [submatrix_apply,Equiv.symm_apply_apply,Equiv.apply_symm_apply,
    kroneckerMap_apply,Matrix.add_apply,Matrix.one_apply,
    (finProdFinEquiv : Fin p.c × Fin D ≃ Fin (p.c*D)).injective.eq_iff,
    p.split.symm.injective.eq_iff,Prod.mk.injEq,FactoryPhysicalHamiltonian.indicator_and]
  ring

end ScheduleLaw.Blueprint.PhaseHardwareEnergy
