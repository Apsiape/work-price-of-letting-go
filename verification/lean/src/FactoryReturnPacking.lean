import FactoryPackedFormation
import FactoryRegisterReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped Classical BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.FactoryReturnPacking
open History FactoryRegisters FactoryPacking FactoryPackedFormation

def restGather {b c t1 t2 t4 : Type} :
    (Rest (b:=b) (t1:=t1) (t2:=t2) (t4:=t4)) × c ≃
      FactoryWorkFlags.Work × (b × (t1 × t2 × t4 × c)) where
  toFun
    | ((batch,w1,w2,w3,w4,bath1,bath2,bath4),fresh) =>
      ((w1,w2,w3,w4),batch,bath1,bath2,bath4,fresh)
  invFun
    | ((w1,w2,w3,w4),batch,bath1,bath2,bath4,fresh) =>
      ((batch,w1,w2,w3,w4,bath1,bath2,bath4),fresh)
  left_inv _ := rfl
  right_inv _ := rfl

def restFrame (d m D r1 r2 r4 : ℕ) :
    (Rest (b:=Fin m → Fin d) (t1:=Fin r1) (t2:=Fin r2) (t4:=Fin r4)) × Fin D ≃
      Fin 16 × Fin ((Fintype.card (Fin m → Fin d))*auxSize D r1 r2 r4) :=
  restGather.trans (Equiv.prodCongr workEquiv
    ((Equiv.prodCongr (Equiv.refl _) (auxEquiv D r1 r2 r4)).trans
      (FactoryFormation.reservoirSplit d m (auxSize D r1 r2 r4)).symm))

theorem frame_reset {d m D r1 r2 r4 : ℕ}
    (z : Registers (Fin m → Fin d) (Fin D) (Fin r1) (Fin r2) (Fin r4)) :
    FactoryPacking.frame d m D r1 r2 r4 z =
      ((resetFrame z).1,restFrame d m D r1 r2 r4 (resetFrame z).2) := rfl

theorem inverse_frame {d m D r1 r2 r4 : ℕ}
    (z : Fin D × (Fin 16 × Fin ((Fintype.card (Fin m → Fin d))*auxSize D r1 r2 r4))) :
    resetFrame ((FactoryPacking.frame d m D r1 r2 r4).symm z) =
      (z.1,(restFrame d m D r1 r2 r4).symm z.2) := by
  apply (Equiv.prodCongr (Equiv.refl (Fin D)) (restFrame d m D r1 r2 r4)).injective
  change ((resetFrame _).1,restFrame d m D r1 r2 r4 (resetFrame _).2)=_
  rw [← frame_reset,Equiv.apply_symm_apply]
  simp only [Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,Equiv.apply_symm_apply,Prod.mk.eta]

/-- Physical reset return transported to Formation's exact controller/work/reservoir split. -/
theorem packed_return {d m D r1 r2 r4 : ℕ} (hD : 0 < D)
    (batch : Density (Fin m → Fin d))
    (γ1 : Density (Fin r1)) (γ2 : Density (Fin r2)) (γ4 : Density (Fin r4))
    {r : Type} [Fintype r] [DecidableEq r] (e : Fin D ≃ (Fin m → Fin d) × r)
    (U1 : Mat ((Fin m → Fin d) × (Fin 2 × Fin r1)))
    (U2 : Mat (Fin D × (Fin 2 × Fin r2))) (V : Mat (Fin D))
    (U4 : Mat (Fin D × (Fin 2 × Fin r4)))
    (h1 : IsUnitary U1) (h2 : IsUnitary U2) (hV : IsUnitary V) (h4 : IsUnitary U4) :
    ∃ ω : Density (Fin 16 × Fin ((Fintype.card (Fin m → Fin d))*auxSize D r1 r2 r4)),
      (evolve (circuit e U1 U2 V U4)
        (FactoryInitializer.matrix (FactoryFormation.flat D hD) batch γ1 γ2 γ4
          (FactoryFormation.flat D hD))).submatrix
        (FactoryPacking.frame d m D r1 r2 r4).symm
        (FactoryPacking.frame d m D r1 r2 r4).symm =
        (FactoryFormation.flat D hD).matrix ⊗ₖ ω.matrix := by
  obtain ⟨σ,hσ⟩ := FactoryRegisterReturn.circuit_return e (FactoryFormation.flat D hD)
    batch γ1 γ2 γ4 (FactoryFormation.flat D hD) U1 U2 V U4 h1 h2 hV h4
  let ω : Density (Fin 16 × Fin ((Fintype.card (Fin m → Fin d))*auxSize D r1 r2 r4)) :=
    ⟨σ.matrix.submatrix (restFrame d m D r1 r2 r4).symm (restFrame d m D r1 r2 r4).symm,
      σ.positive.submatrix _,by rw [submatrix_trace_equiv,σ.normalized]⟩
  refine ⟨ω,?_⟩
  ext i j
  have hh := congrArg (fun A => A
    (resetFrame ((FactoryPacking.frame d m D r1 r2 r4).symm i))
    (resetFrame ((FactoryPacking.frame d m D r1 r2 r4).symm j))) hσ
  simp only [submatrix_apply,Equiv.symm_apply_apply] at hh
  rw [inverse_frame,inverse_frame] at hh
  exact hh

end ScheduleLaw.Blueprint.FactoryReturnPacking
