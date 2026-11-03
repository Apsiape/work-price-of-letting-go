import FlatOutput
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped BigOperators Kronecker ComplexOrder Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FiniteFlat

def sourceWeight (β : ℝ) (d k L : ℕ) (r : Fin (bathSize d k L)) : ℂ :=
  ((Real.exp (-β*bathEnergy β d k L r)/(((L : ℝ)+1)*(k : ℝ)^L) : ℝ) : ℂ)
def outputWeight (β : ℝ) (d k L : ℕ) (hkd : k ≤ d) (i : Fin d) (r : Fin (bathSize d k L)) : ℂ :=
  if (ladderPermutation d k L hkd (i,1,r)).2.1=0 then
    (d : ℂ)⁻¹*sourceWeight β d k L (ladderPermutation d k L hkd (i,1,r)).2.2 else 0

theorem constructed_output (β : ℝ) (hβ : 0<β) (d k L : ℕ) (hd : 0<d) (hk : 0<k) (hkd : k ≤ d) :
    flatOutput ((constructedLadder β d k L hkd).converter hk) =
      diagonal (fun i => ∑ r : Fin (bathSize d k L),outputWeight β d k L hkd i r) := by
  let C : SupportConverter β (zeroHamiltonian d) (-gap β d k) :=
    (constructedLadder β d k L hkd).converter hk
  have hU : C.U=(ladderPermutation d k L hkd).permMatrix ℂ := rfl
  have hγ : gibbs β C.HR=diagonal (sourceWeight β d k L) := bath_gibbs β hβ d k L hd hk
  exact FlatOutput.output_permutation C (ladderPermutation d k L hkd) (sourceWeight β d k L) hU hγ

lemma lower_cap_fixed (d k L : ℕ) (hkd : k ≤ d) (i : Fin d) (r : Fin (multiplicity d k L 0)) :
    ladderPermutation d k L hkd (i,1,Fintype.equivFin (Bath d k L) ⟨0,r⟩) =
      (i,1,Fintype.equivFin (Bath d k L) ⟨0,r⟩) := by
  change FiniteSwap.apply (initialColumn d k L) (finalColumn d k L hkd) _ = _
  apply FiniteSwap.outside
  · rintro ⟨x,hx⟩
    have hb:=congrArg (fun z : Hardware d k L => z.2.1.val) hx
    change (0 : ℕ)=1 at hb
    omega
  · rintro ⟨y,hy⟩
    have hb:=(Fintype.equivFin (Bath d k L)).injective (congrArg (fun z : Hardware d k L => z.2.2) hy)
    have hl:=congrArg (fun b : Bath d k L => b.1.val) hb
    change y.1.val+1=0 at hl
    omega
lemma output_bottom (β : ℝ) (d k L : ℕ) (hkd : k ≤ d) (i : Fin d) (r : Fin (multiplicity d k L 0)) :
    outputWeight β d k L hkd i (Fintype.equivFin (Bath d k L) ⟨0,r⟩) = 0 := by
  unfold outputWeight
  rw [lower_cap_fixed]
  norm_num
lemma output_outside (β : ℝ) (d k L : ℕ) (hkd : k ≤ d) (i : Fin d) (hi : k ≤ i.val)
    (r : Fin (bathSize d k L)) : outputWeight β d k L hkd i r=0 := by
  unfold outputWeight
  rw [outside_rank_fixed d k L hkd i hi r]
  norm_num
lemma output_destination (β : ℝ) (d k L : ℕ) (hkd : k ≤ d) (i : Fin d) (hi : i.val<k)
    (j : Fin L) (r : Fin (multiplicity d k L (j.val+1))) :
    outputWeight β d k L hkd i (Fintype.equivFin (Bath d k L) ⟨j.succ,r⟩) =
      (d : ℂ)⁻¹*((Real.exp (-β*(gap β d k*(j.val : ℝ)))/(((L : ℝ)+1)*(k : ℝ)^L) : ℝ) : ℂ) := by
  let y : Targets d k L := ⟨j,⟨⟨i.val,hi⟩,r⟩⟩
  change (if (ladderPermutation d k L hkd (destinationColumn d k L hkd y)).2.1=0 then
    (d : ℂ)⁻¹*sourceWeight β d k L (ladderPermutation d k L hkd (destinationColumn d k L hkd y)).2.2 else 0) = _
  rw [destinationColumn_swapped]
  simp only [initialColumn,sourceWeight,bathEnergy,Equiv.symm_apply_apply]
  change (if (0 : Fin 2)=0 then (d : ℂ)⁻¹*
    ((Real.exp (-β*(gap β d k*(j.val : ℝ)))/(((L : ℝ)+1)*(k : ℝ)^L) : ℝ) : ℂ) else 0) = _
  simp

lemma target_shell_weight (β : ℝ) (hβ : 0<β) (d k L : ℕ) (hd : 0<d) (hk : 0<k) (j : Fin L) :
    (multiplicity d k L (j.val+1) : ℂ)*((d : ℂ)⁻¹*
      ((Real.exp (-β*(gap β d k*(j.val : ℝ)))/(((L : ℝ)+1)*(k : ℝ)^L) : ℝ) : ℂ)) =
        ((1/((k : ℝ)*((L : ℝ)+1)) : ℝ) : ℂ) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hl0 : (L : ℝ)+1 ≠ 0 := by positivity
  let e : ℝ := Real.exp (-β*(gap β d k*(j.val : ℝ)))
  have hc : (k : ℝ)*(multiplicity d k L (j.val+1) : ℝ) =
      (d : ℝ)*(multiplicity d k L j.val : ℝ) := by exact_mod_cast (capacity d k L j.val j.isLt).symm
  have hw : (k : ℝ)*(multiplicity d k L (j.val+1) : ℝ)*e = (d : ℝ)*(k : ℝ)^L := by
    rw [hc,mul_assoc,shell_weight β hβ d k L j.val hd hk j.isLt.le]
  have hge : (multiplicity d k L (j.val+1) : ℝ)*e = (d : ℝ)*(k : ℝ)^L/(k : ℝ) := by
    apply (eq_div_iff hk0).mpr
    nlinarith only [hw]
  have hh : (multiplicity d k L (j.val+1) : ℝ)*((d : ℝ)⁻¹*
      (e/(((L : ℝ)+1)*(k : ℝ)^L))) = 1/((k : ℝ)*((L : ℝ)+1)) := by
    calc _ = ((multiplicity d k L (j.val+1) : ℝ)*e)/
        ((d : ℝ)*(((L : ℝ)+1)*(k : ℝ)^L)) := by
          simp only [div_eq_mul_inv,_root_.mul_inv_rev]
          ring
         _ = ((d : ℝ)*(k : ℝ)^L/(k : ℝ))/
             ((d : ℝ)*(((L : ℝ)+1)*(k : ℝ)^L)) := by rw [hge]
         _ = _ := by field_simp [hd0,hk0,hl0]
  have hh' := congrArg (fun x : ℝ => (x : ℂ)) hh
  simpa only [e,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_natCast] using hh'

lemma output_below (β : ℝ) (hβ : 0<β) (d k L : ℕ) (hd : 0<d) (hk : 0<k) (hkd : k ≤ d)
    (i : Fin d) (hi : i.val<k) :
    (∑ r : Fin (bathSize d k L),outputWeight β d k L hkd i r) = ((successRate L/k : ℝ) : ℂ) := by
  classical
  have he : (∑ r : Fin (bathSize d k L),outputWeight β d k L hkd i r) =
      ∑ b : Bath d k L,outputWeight β d k L hkd i (Fintype.equivFin (Bath d k L) b) :=
    (Equiv.sum_comp (Fintype.equivFin (Bath d k L)) _).symm
  rw [he]
  have hs : (∑ b : Bath d k L,outputWeight β d k L hkd i (Fintype.equivFin (Bath d k L) b)) =
      ∑ j : Fin (L+1),∑ r : Fin (multiplicity d k L j.val),
        outputWeight β d k L hkd i (Fintype.equivFin (Bath d k L) ⟨j,r⟩) :=
    Fintype.sum_sigma _
  rw [hs,Fin.sum_univ_succ]
  simp only [output_bottom,Finset.sum_const_zero,zero_add]
  simp_rw [output_destination β d k L hkd i hi]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [Fin.val_succ]
  simp_rw [target_shell_weight β hβ d k L hd hk]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hl0 : (L : ℝ)+1 ≠ 0 := by positivity
  have hh : (L : ℝ)*(1/((k : ℝ)*((L : ℝ)+1))) = successRate L/k := by
    unfold successRate
    field_simp [hk0,hl0]
  have hh' := congrArg (fun x : ℝ => (x : ℂ)) hh
  simpa only [Complex.ofReal_mul,Complex.ofReal_natCast] using hh'

theorem exact_constructed_output (β : ℝ) (hβ : 0<β) (d k L : ℕ) (hd : 0<d) (hk : 0<k) (hkd : k ≤ d) :
    flatOutput ((constructedLadder β d k L hkd).converter hk) =
      (((successRate L/k : ℝ) : ℂ) • rankProjection d k) := by
  rw [constructed_output β hβ d k L hd hk hkd]
  ext i j
  by_cases hij : i=j
  · subst j
    by_cases hi : i.val<k
    · simpa [rankProjection,hi] using output_below β hβ d k L hd hk hkd i hi
    · simp [rankProjection,hi,output_outside β d k L hkd i (Nat.le_of_not_gt hi)]
  · simp [rankProjection,Matrix.diagonal,hij]
end ScheduleLaw.Blueprint.FiniteFlat
