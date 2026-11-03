import SupportConversion
import SupportRunGeneral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder
namespace ScheduleLaw.Blueprint
open History
namespace SupportBathReindex
open History

theorem physical_converter_certified {d : ℕ} {c : Type} [Fintype c] [DecidableEq c] [Nonempty c]
    (β x f : ℝ) (H : Hamiltonian (Fin d)) (P Q : Mat (Fin d))
    (R : c → ℝ) (G : Mat c) (U : Mat (Fin d × (Fin 2 × c)))
    (hU : IsUnitary U)
    (hcon : Conserves U (H.matrix ⊗ₖ (1 : Mat (Fin 2 × c)) +
      (1 : Mat (Fin d)) ⊗ₖ ((diagonal ![0,(x : ℂ)]) ⊗ₖ (1 : Mat c) +
        (1 : Mat (Fin 2)) ⊗ₖ (diagonal (fun k => (R k : ℂ))))))
    (hgap : (Uᴴ*(Q ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat c)))*U -
      P ⊗ₖ (SupportRun.level 0 ⊗ₖ G)).PosSemidef)
    (hstock : 1-f ≤ energy G (gibbs β (FlatMatrix.diagonalHamiltonian c R))) :
    ∃ C : SupportConverter β H x, SupportRun.EffectCertificate C P Q f := by
  let r := Fintype.card c
  let e : Fin r ≃ c := (Fintype.equivFin c).symm
  let J : (Fin d × (Fin 2 × Fin r)) ≃ (Fin d × (Fin 2 × c)) :=
    Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) e)
  let HR := FlatMatrix.diagonalHamiltonian (Fin r) (R ∘ e)
  have hH : converterHamiltonian H HR x =
      (H.matrix ⊗ₖ (1 : Mat (Fin 2 × c)) + (1 : Mat (Fin d)) ⊗ₖ
        ((diagonal ![0,(x : ℂ)]) ⊗ₖ (1 : Mat c) +
          (1 : Mat (Fin 2)) ⊗ₖ (diagonal (fun k => (R k : ℂ))))).submatrix J J := by
    ext ⟨i,⟨w,k⟩⟩ ⟨j,⟨v,h⟩⟩
    simp [converterHamiltonian,HR,FlatMatrix.diagonalHamiltonian,J,
      Matrix.diagonal,Matrix.one_apply,e.injective.eq_iff]
  let C : SupportConverter β H x := {
    r := r
    r_pos := Fintype.card_pos
    HR := HR
    U := U.submatrix J J
    unitary := unitary_submatrix J hU
    conserves := by rw [hH]; exact conserves_reindex J U _ hcon }
  let Gf := G.submatrix e e
  have hsuc : (Q ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat c))).submatrix J J =
      Q ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin r))) := by
    ext ⟨i,⟨w,k⟩⟩ ⟨j,⟨v,h⟩⟩
    simp [J,Matrix.one_apply,e.injective.eq_iff]
  have hinit : (P ⊗ₖ (SupportRun.level 0 ⊗ₖ G)).submatrix J J =
      P ⊗ₖ (SupportRun.level 0 ⊗ₖ Gf) := rfl
  have hgfin : (C.Uᴴ*(Q ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r))))*C.U -
      P ⊗ₖ (SupportRun.level 0 ⊗ₖ Gf)).PosSemidef := by
    have h := hgap.submatrix J
    simp only [submatrix_sub,Pi.sub_apply] at h
    rw [← submatrix_mul_equiv _ _ J J J,← submatrix_mul_equiv _ _ J J J,hsuc,hinit] at h
    simpa only [C,conjTranspose_submatrix] using h
  have hp : energy Gf (gibbs β C.HR) = energy G (gibbs β (FlatMatrix.diagonalHamiltonian c R)) := by
    change energy (G.submatrix e e) (gibbs β HR) = _
    rw [diagonal_gibbs_reindex,energy_reindex]
  exact ⟨C,Gf,hgfin,by rw [hp]; exact hstock⟩

end SupportBathReindex

namespace SupportHardware
open History SupportPhysicalFrame

theorem from_coordinates_certified {d : ℕ} {c : Type} [Fintype c] [DecidableEq c] [Nonempty c]
    (β x f : ℝ) (H : Hamiltonian (Fin d)) (P Q UP UQ : Mat (Fin d))
    (EP EQ : Fin d → ℝ) (TP TQ : Finset (Fin d))
    (hUP : IsUnitary UP) (hUQ : IsUnitary UQ)
    (hHP : H.matrix=evolve UP (diagonal (fun i => (EP i : ℂ))))
    (hHQ : H.matrix=evolve UQ (diagonal (fun i => (EQ i : ℂ))))
    (hP : P=evolve UP (diagonal (fun i => if i∈TP then 1 else 0)))
    (hQ : Q=evolve UQ (diagonal (fun i => if i∈TQ then 1 else 0)))
    (R : c → ℝ) (G : Mat c) (U : Mat (Fin d × (Fin 2 × c)))
    (hU : IsUnitary U)
    (hcon : Conserves U (diagonal (fun z : Fin d × (Fin 2 × c) =>
      (((if z.2.1=0 then EP z.1 else EQ z.1+x)+R z.2.2 : ℝ) : ℂ))))
    (hgap : (Uᴴ*((diagonal (fun i => if i∈TQ then 1 else 0)) ⊗ₖ
      (SupportRun.level 1 ⊗ₖ (1 : Mat c)))*U -
        (diagonal (fun i => if i∈TP then 1 else 0)) ⊗ₖ (SupportRun.level 0 ⊗ₖ G)).PosSemidef)
    (hstock : 1-f ≤ energy G (gibbs β (FlatMatrix.diagonalHamiltonian c R))) :
    ∃ C : SupportConverter β H x, SupportRun.EffectCertificate C P Q f := by
  let V (w : Fin 2) := if w=0 then UP else UQ
  let W := frame (c:=c) V
  have hV (w : Fin 2) : IsUnitary (V w) := by
    dsimp [V]; split_ifs <;> assumption
  have hW : IsUnitary W := frame_unitary V hV
  have hs : evolve W ((diagonal (fun i => if i∈TQ then 1 else 0)) ⊗ₖ
      (SupportRun.level 1 ⊗ₖ (1 : Mat c))) = Q ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat c)) := by
    rw [frame_level]
    simpa only [V,(by decide : (1 : Fin 2)≠0),if_false] using congrArg
      (fun A => A ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat c))) hQ.symm
  have hi : evolve W ((diagonal (fun i => if i∈TP then 1 else 0)) ⊗ₖ
      (SupportRun.level 0 ⊗ₖ G)) = P ⊗ₖ (SupportRun.level 0 ⊗ₖ G) := by
    rw [frame_level]
    simpa only [V,if_true] using congrArg
      (fun A => A ⊗ₖ (SupportRun.level 0 ⊗ₖ G)) hP.symm
  let D : Mat (Fin d × (Fin 2 × c)) := diagonal (fun z =>
    (((if z.2.1=0 then EP z.1 else EQ z.1+x)+R z.2.2 : ℝ) : ℂ))
  have hHam : evolve W D = H.matrix ⊗ₖ (1 : Mat (Fin 2 × c)) +
      (1 : Mat (Fin d)) ⊗ₖ ((diagonal ![0,(x : ℂ)]) ⊗ₖ (1 : Mat c) +
        (1 : Mat (Fin 2)) ⊗ₖ (diagonal (fun k => (R k : ℂ)))) := by
    have h := frame_hamiltonian (c:=c) V hV H.matrix
      (fun w => if w=0 then EP else EQ) R (fun w => if w=0 then 0 else x)
      (by intro w; dsimp [V]; split_ifs
          · exact hHP.symm
          · exact hHQ.symm)
    have hd : diagonal (fun z : Fin d × (Fin 2 × c) =>
        (((if z.2.1=0 then EP else EQ) z.1+(if z.2.1=0 then 0 else x)+R z.2.2 : ℝ) : ℂ)) = D := by
      congr 1
      funext z
      by_cases hw : z.2.1=0 <;> simp [hw]
    have hx : (fun w : Fin 2 => ((if w=0 then 0 else x : ℝ) : ℂ)) = ![0,(x : ℂ)] := by
      funext w; fin_cases w <;> simp
    rw [hd,hx] at h
    exact h
  have hg := conjugate_effect W U _ _ hW hgap
  rw [hs,hi] at hg
  apply SupportBathReindex.physical_converter_certified β x f H P Q R G (W*U*Wᴴ)
    (unitary_mul (unitary_mul hW hU) (FiniteFlat.adjoint_unitary hW)) _ hg hstock
  rw [← hHam]
  exact conjugate_conserves W U D hW hcon


end SupportHardware

namespace SupportConversion
open History SupportGenerators

theorem convert_certified {d : ℕ} (_hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (H : Hamiltonian (Fin d)) (P Q : Mat (Fin d))
    (hP : P.IsHermitian) (hPi : P*P=P) (hQ : Q.IsHermitian) (hQi : Q*Q=Q)
    (hPH : P*H.matrix=H.matrix*P) (hQH : Q*H.matrix=H.matrix*Q)
    (hZP : 0 < energy P (boltzmann β H)) (hZQ : 0 < energy Q (boltzmann β H))
    (x f : ℝ) (hx : x < Real.log (energy Q (boltzmann β H)/energy P (boltzmann β H))/β)
    (hf : 0 < f) :
    ∃ C : SupportConverter β H x, SupportRun.EffectCertificate C P Q f := by
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
  exact SupportHardware.from_coordinates_certified β x f H P Q UP UQ EP EQ TP TQ
    hUP hUQ hHP hHQ hPP hQQ R G U hU hcon hgap hstock


theorem convert_general {d : ℕ} (_hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (H : Hamiltonian (Fin d)) (P Q : Mat (Fin d))
    (hP : P.IsHermitian) (hPi : P*P=P) (hQ : Q.IsHermitian) (hQi : Q*Q=Q)
    (hPH : P*H.matrix=H.matrix*P) (hQH : Q*H.matrix=H.matrix*Q)
    (hZP : 0 < energy P (boltzmann β H)) (hZQ : 0 < energy Q (boltzmann β H))
    (x f : ℝ) (hx : x < Real.log (energy Q (boltzmann β H)/energy P (boltzmann β H))/β)
    (hf : 0 < f) :
    ∃ C : SupportConverter β H x, ∀ z (ρ : Density (Fin d × Fin z)),
      (1-f)*energy (P ⊗ₖ (1 : Mat (Fin z))) ρ.matrix ≤ energy ((Q ⊗ₖ (SupportRun.level 1 ⊗ₖ (1 : Mat (Fin C.r)))) ⊗ₖ
        (1 : Mat (Fin z))) (C.run z ρ.matrix)  := by
  obtain ⟨C,hC⟩ := convert_certified _hd β hβ H P Q hP hPi hQ hQi hPH hQH hZP hZQ x f hx hf
  have hp : P.PosSemidef := by
    have h := posSemidef_conjTranspose_mul_self P
    rwa [hP.eq,hPi] at h
  exact ⟨C,fun z ρ => hC.general hp z ρ⟩

end SupportConversion

end ScheduleLaw.Blueprint
