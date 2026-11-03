import SupportHardware
import SupportGenerators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint.SupportConversion
open History SupportGenerators

theorem convert {d : ℕ} (_hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (H : Hamiltonian (Fin d)) (P Q : Mat (Fin d))
    (hP : P.IsHermitian) (hPi : P*P=P) (hQ : Q.IsHermitian) (hQi : Q*Q=Q)
    (hPH : P*H.matrix=H.matrix*P) (hQH : Q*H.matrix=H.matrix*Q)
    (hZP : 0 < energy P (boltzmann β H)) (hZQ : 0 < energy Q (boltzmann β H))
    (x f : ℝ) (hx : x < Real.log (energy Q (boltzmann β H)/energy P (boltzmann β H))/β)
    (hf : 0 < f) :
    ∃ C : SupportConverter β H x, ∀ z (ρ : Density (Fin d × Fin z)),
      (P ⊗ₖ (1 : Mat (Fin z)))*ρ.matrix=ρ.matrix →
      1-f ≤ energy ((Q ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r)))) ⊗ₖ
        (1 : Mat (Fin z))) (C.run z ρ.matrix) := by
  obtain ⟨UP,EP,TP,hUP,hHP,hPP,hZPe⟩ := SupportBasis.support_coordinates β H P hP hPi hPH
  obtain ⟨UQ,EQ,TQ,hUQ,hHQ,hQQ,hZQe⟩ := SupportBasis.support_coordinates β H Q hQ hQi hQH
  let s := d+(d+1)
  let ω := generators EP EQ x
  let ds (i : Fin d) := direction (sourceIndex i)
  let dt (i : Fin d) := direction (targetIndex i)
  let dx := direction (workIndex d)
  have hs (i : Fin d) : SupportTiles.coordinateEnergy ω (ds i)=EP i := source_energy EP EQ x i
  have ht (i : Fin d) : SupportTiles.coordinateEnergy ω (dt i)=EQ i := target_energy EP EQ x i
  have hw : SupportTiles.coordinateEnergy ω dx=x := work_energy EP EQ x
  obtain ⟨θ,N,K,g,E0,hθ,hθ1,hN,hK,hg,hbounds,hcap,hE0,hE,hstock⟩ :=
    SupportStock.prepared_stock s ω β (energy P (boltzmann β H))
      (energy Q (boltzmann β H)) x f hβ hZP hZQ hx hf
  have hcap' : (∑ i : {i : Fin d // i∈TP},Real.exp (-β*SupportTiles.coordinateEnergy ω (ds i))) <
      (1-θ)*Real.exp (-β*SupportTiles.coordinateEnergy ω dx)*
        (∑ i : {i : Fin d // i∈TQ},Real.exp (-β*SupportTiles.coordinateEnergy ω (dt i))) := by
    simp only [hs,ht,hw]
    rw [hZPe,hZQe] at hcap
    rw [← Finset.sum_subtype TP (fun _ => Iff.rfl) (fun i => Real.exp (-β*EP i)),
      ← Finset.sum_subtype TQ (fun _ => Iff.rfl) (fun i => Real.exp (-β*EQ i))]
    exact hcap
  obtain ⟨U,hU,hcon,hgap⟩ := SupportTiledGate.conserving_gate d s N K ω ds dt dx TP TQ g
    β θ E0 hK hbounds (fun i j k => shift_bound i j k) hcap'
  let c := SupportTiles.Bath g
  let R (b : c) := E0+SupportTiles.coordinateEnergy ω (SupportBox.coordinates (Fin s) b.1)
  let G := SupportTiles.goodProjector g (SupportBox.good (Fin s) N)
  letI : Nonempty c := ⟨⟨(fun _ => 0),⟨0,hg _⟩⟩⟩
  have he : diagonal (fun z : Fin d × (Fin 2 × c) =>
      (SupportTiledGate.frameEnergy ω ds dt dx g E0 z : ℂ)) =
      diagonal (fun z => (((if z.2.1=0 then EP z.1 else EQ z.1+x)+R z.2.2 : ℝ) : ℂ)) := by
    congr 1
    funext z
    unfold SupportTiledGate.frameEnergy
    simp only [hs,ht,hw,R]
    congr 1
    split_ifs <;> ring
  rw [he] at hcon
  have hsuccess : diagonal (fun z : Fin d × (Fin 2 × c) => if z.2.1=1 ∧ z.1∈TQ then 1 else 0) =
      diagonal (fun i => if i∈TQ then 1 else 0) ⊗ₖ
        (SupportRun.level 1 ⊗ₖ (1 : Mat c)) := by
    have h := SupportHardware.diagonal_mask (fun i : Fin d => i∈TQ) (fun _ : c => True) 1
    simpa only [and_true,true_and,if_true,diagonal_one,and_comm] using h
  have hinitial : diagonal (fun z : Fin d × (Fin 2 × c) =>
      if z.1∈TP ∧ z.2.1=0 ∧ z.2.2.1∈SupportBox.good (Fin s) N then 1 else 0) =
      diagonal (fun i => if i∈TP then 1 else 0) ⊗ₖ (SupportRun.level 0 ⊗ₖ G) :=
    SupportHardware.diagonal_mask (fun i : Fin d => i∈TP)
      (fun b : c => b.1∈SupportBox.good (Fin s) N) 0
  rw [hsuccess,hinitial] at hgap
  exact SupportHardware.from_coordinates β x f H P Q UP UQ EP EQ TP TQ
    hUP hUQ hHP hHQ hPP hQQ R G U hU hcon hgap hstock

end ScheduleLaw.Blueprint.SupportConversion
