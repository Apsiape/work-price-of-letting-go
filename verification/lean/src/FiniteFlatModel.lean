import FlatGibbs

/-! Full exact flat-converter route. The bath is the literal finite collection
of shells d^j*k^(L-j), with a fixed Hamiltonian and both battery labels.
Open declarations are explicit blueprint obligations, never external inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint.FiniteFlat

def multiplicity (d k L j : ℕ) : ℕ := d^j*k^(L-j)
def Bath (d k L : ℕ) := (j : Fin (L+1)) × Fin (multiplicity d k L j.val)
instance (d k L : ℕ) : Fintype (Bath d k L) := by unfold Bath; infer_instance
instance (d k L : ℕ) : DecidableEq (Bath d k L) := Classical.decEq _
def bathSize (d k L : ℕ) : ℕ := Fintype.card (Bath d k L)
def gap (β : ℝ) (d k : ℕ) : ℝ := Real.log ((d : ℝ)/k)/β
def successRate (L : ℕ) : ℝ := (L : ℝ)/(L+1)
def rankProjection (d k : ℕ) : Mat (Fin d) := diagonal (fun i => if i.val<k then 1 else 0)

theorem capacity (d k L j : ℕ) (hj : j<L) :
    d*multiplicity d k L j = k*multiplicity d k L (j+1) := by
  unfold multiplicity
  rw [show L-j=L-(j+1)+1 by omega,pow_succ,pow_succ]
  ring

def shellEquiv (d k L : ℕ) (j : Fin L) :
    (Fin d × Fin (multiplicity d k L j.val)) ≃
      (Fin k × Fin (multiplicity d k L (j.val+1))) :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_prod,Fintype.card_fin] using capacity d k L j.val j.isLt)

theorem bathSize_pos (d k L : ℕ) (hk : 0<k) : 0<bathSize d k L := by
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨0,⟨0,?_⟩⟩⟩
  simpa only [multiplicity,Fin.val_zero,pow_zero,Nat.sub_zero,one_mul] using pow_pos hk L

def bathEnergy (β : ℝ) (d k L : ℕ) (i : Fin (bathSize d k L)) : ℝ :=
  gap β d k * (((Fintype.equivFin (Bath d k L)).symm i).1.val : ℝ)
def bathHamiltonian (β : ℝ) (d k L : ℕ) : Hamiltonian (Fin (bathSize d k L)) :=
  ⟨diagonal (fun i => (bathEnergy β d k L i : ℂ)),by
    ext i j
    by_cases h : i=j
    · subst j; simp
    · simp [Matrix.diagonal,h,Ne.symm h]⟩

def zeroHamiltonian (d : ℕ) : Hamiltonian (Fin d) := ⟨0,by simp⟩

def flatOutput {d : ℕ} {β x : ℝ} (C : SupportConverter β (zeroHamiltonian d) x) : Mat (Fin d) :=
  partialRight (partialRight ((
    ((1 : Mat (Fin d)) ⊗ₖ (pureMatrix (fun j : Fin 2 => if j=1 then 1 else 0) ⊗ₖ
      (1 : Mat (Fin C.r)))) ⊗ₖ (1 : Mat (Fin 1))) *
    C.run 1 ((((d : ℂ)⁻¹) • (1 : Mat (Fin d))) ⊗ₖ (1 : Mat (Fin 1)))))

structure Ladder (β : ℝ) (d k L : ℕ) where
  U : Mat (Fin d × (Fin 2 × Fin (bathSize d k L)))
  unitary : IsUnitary U
  conserves : Conserves U (converterHamiltonian (zeroHamiltonian d)
    (bathHamiltonian β d k L) (-gap β d k))

def Ladder.converter {β : ℝ} {d k L : ℕ} (D : Ladder β d k L) (hk : 0<k) :
    SupportConverter β (zeroHamiltonian d) (-gap β d k) where
  r := bathSize d k L
  r_pos := bathSize_pos d k L hk
  HR := bathHamiltonian β d k L
  U := D.U
  unitary := D.unitary
  conserves := D.conserves

/-- Exact Gibbs weight of every shell before normalization. -/
theorem shell_weight (β : ℝ) (hβ : 0<β) (d k L j : ℕ)
    (hd : 0<d) (hk : 0<k) (hj : j ≤ L) :
    (multiplicity d k L j : ℝ)*Real.exp (-β*(gap β d k*(j : ℝ))) = (k : ℝ)^L := by
  have hdz : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hr : 0<(d : ℝ)/k := by positivity
  have he : -β*(gap β d k*(j : ℝ)) = (j : ℝ)*(-Real.log ((d : ℝ)/k)) := by
    unfold gap
    field_simp
  rw [he,Real.exp_nat_mul,Real.exp_neg,Real.exp_log hr]
  simp only [multiplicity,Nat.cast_mul,Nat.cast_pow,inv_div]
  calc (d : ℝ)^j*(k : ℝ)^(L-j)*((k : ℝ)/d)^j =
      ((d : ℝ)^j/(d : ℝ)^j)*((k : ℝ)^(L-j)*(k : ℝ)^j) := by rw [div_pow]; ring
       _ = (k : ℝ)^L := by
         rw [div_self (pow_ne_zero _ hdz),one_mul,←pow_add,Nat.sub_add_cancel hj]

theorem bath_partition (β : ℝ) (hβ : 0<β) (d k L : ℕ) (hd : 0<d) (hk : 0<k) :
    (∑ i : Fin (bathSize d k L),Real.exp (-β*bathEnergy β d k L i)) =
      ((L : ℝ)+1)*(k : ℝ)^L := by
  classical
  have he : (∑ i : Fin (bathSize d k L),Real.exp (-β*bathEnergy β d k L i)) =
      ∑ b : Bath d k L,Real.exp (-β*(gap β d k*(b.1.val : ℝ))) := by
    calc _ = ∑ b : Bath d k L,Real.exp (-β*bathEnergy β d k L
        (Fintype.equivFin (Bath d k L) b)) :=
          (Equiv.sum_comp (Fintype.equivFin (Bath d k L))
            (fun i : Fin (bathSize d k L) => Real.exp (-β*bathEnergy β d k L i))).symm
         _ = _ := by simp only [bathEnergy,Equiv.symm_apply_apply]
  rw [he]
  have hs : (∑ b : Bath d k L,Real.exp (-β*(gap β d k*(b.1.val : ℝ)))) =
      ∑ j : Fin (L+1),∑ _u : Fin (multiplicity d k L j.val),
        Real.exp (-β*(gap β d k*(j.val : ℝ))) :=
    Fintype.sum_sigma (fun b : Sigma (fun j : Fin (L+1) => Fin (multiplicity d k L j.val)) =>
      Real.exp (-β*(gap β d k*(b.1.val : ℝ))))
  rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  calc (∑ j : Fin (L+1),(multiplicity d k L j.val : ℝ)*
      Real.exp (-β*(gap β d k*(j.val : ℝ)))) = ∑ _j : Fin (L+1),(k : ℝ)^L := by
        apply Finset.sum_congr rfl
        intro j hj
        exact shell_weight β hβ d k L j.val hd hk (by have h:=j.isLt; omega)
       _ = ((L : ℝ)+1)*(k : ℝ)^L := by simp

theorem bath_gibbs (β : ℝ) (hβ : 0<β) (d k L : ℕ) (hd : 0<d) (hk : 0<k) :
    gibbs β (bathHamiltonian β d k L) = diagonal (fun i =>
      ((Real.exp (-β*bathEnergy β d k L i)/(((L : ℝ)+1)*(k : ℝ)^L) : ℝ) : ℂ)) := by
  change gibbs β (FlatMatrix.diagonalHamiltonian _ (bathEnergy β d k L)) = _
  rw [FlatMatrix.diagonal_gibbs,bath_partition β hβ d k L hd hk]

def goodTiles (d k L : ℕ) : Mat (Fin (bathSize d k L)) := diagonal (fun i =>
  if ((Fintype.equivFin (Bath d k L)).symm i).1.val < L then 1 else 0)

theorem good_probability (β : ℝ) (hβ : 0<β) (d k L : ℕ) (hd : 0<d) (hk : 0<k) :
    energy (goodTiles d k L) (gibbs β (bathHamiltonian β d k L)) = successRate L := by
  classical
  let Z : ℝ := ((L : ℝ)+1)*(k : ℝ)^L
  rw [bath_gibbs β hβ d k L hd hk]
  unfold energy goodTiles
  rw [diagonal_mul_diagonal,trace_diagonal]
  simp only [Complex.re_sum,ite_mul,one_mul,zero_mul,apply_ite,Complex.ofReal_re,Complex.zero_re]
  have he : (∑ i : Fin (bathSize d k L),
      if ((Fintype.equivFin (Bath d k L)).symm i).1.val<L then
        Real.exp (-β*bathEnergy β d k L i)/Z else 0) =
      ∑ b : Bath d k L, if b.1.val<L then Real.exp (-β*(gap β d k*(b.1.val : ℝ)))/Z else 0 := by
    calc _ = ∑ b : Bath d k L,
        if ((Fintype.equivFin (Bath d k L)).symm (Fintype.equivFin (Bath d k L) b)).1.val<L then
          Real.exp (-β*bathEnergy β d k L (Fintype.equivFin (Bath d k L) b))/Z else 0 :=
            (Equiv.sum_comp (Fintype.equivFin (Bath d k L)) _).symm
         _ = _ := by simp only [bathEnergy,Equiv.symm_apply_apply]
  change (∑ i : Fin (bathSize d k L),
    if ((Fintype.equivFin (Bath d k L)).symm i).1.val<L then
      Real.exp (-β*bathEnergy β d k L i)/Z else 0) = _
  rw [he]
  have hs : (∑ b : Bath d k L,if b.1.val<L then Real.exp (-β*(gap β d k*(b.1.val : ℝ)))/Z else 0) =
      ∑ j : Fin (L+1),∑ _u : Fin (multiplicity d k L j.val),
        if j.val<L then Real.exp (-β*(gap β d k*(j.val : ℝ)))/Z else 0 :=
    Fintype.sum_sigma (fun b : Sigma (fun j : Fin (L+1) => Fin (multiplicity d k L j.val)) =>
      if b.1.val<L then Real.exp (-β*(gap β d k*(b.1.val : ℝ)))/Z else 0)
  rw [hs]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_ite,mul_zero]
  have hw (j : Fin (L+1)) : (multiplicity d k L j.val : ℝ)*
      (Real.exp (-β*(gap β d k*(j.val : ℝ)))/Z) = 1/((L : ℝ)+1) := by
    rw [←mul_div_assoc,shell_weight β hβ d k L j.val hd hk (by have h:=j.isLt; omega)]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    have hl0 : (L : ℝ)+1 ≠ 0 := by positivity
    dsimp [Z]
    field_simp [hk0,hl0]
  simp_rw [hw]
  rw [Fin.sum_univ_castSucc]
  simp [successRate,div_eq_mul_inv]

abbrev Columns (d k L : ℕ) := (j : Fin L) × (Fin d × Fin (multiplicity d k L j.val))
abbrev Targets (d k L : ℕ) := (j : Fin L) × (Fin k × Fin (multiplicity d k L (j.val+1)))
abbrev Hardware (d k L : ℕ) := Fin d × (Fin 2 × Fin (bathSize d k L))
def transfer (d k L : ℕ) : Columns d k L ≃ Targets d k L :=
  Equiv.sigmaCongrRight (fun j => shellEquiv d k L j)
def initialColumn (d k L : ℕ) (x : Columns d k L) : Hardware d k L :=
  (x.2.1,0,Fintype.equivFin (Bath d k L) ⟨⟨x.1.val,by have h:=x.1.isLt; omega⟩,x.2.2⟩)
def destinationColumn (d k L : ℕ) (hkd : k ≤ d) (x : Targets d k L) : Hardware d k L :=
  (⟨x.2.1.val,lt_of_lt_of_le x.2.1.isLt hkd⟩,1,
    Fintype.equivFin (Bath d k L) ⟨⟨x.1.val+1,by have h:=x.1.isLt; omega⟩,x.2.2⟩)
def finalColumn (d k L : ℕ) (hkd : k ≤ d) (x : Columns d k L) : Hardware d k L :=
  destinationColumn d k L hkd (transfer d k L x)
lemma initialColumn_injective (d k L : ℕ) : Function.Injective (initialColumn d k L) := by
  rintro ⟨a,i,u⟩ ⟨b,j,v⟩ he
  have hs:=congrArg (fun x : Hardware d k L => x.1.val) he
  have hb:=(Fintype.equivFin (Bath d k L)).injective (congrArg (fun x : Hardware d k L => x.2.2) he)
  have hlevel:=congrArg (fun x : Bath d k L => x.1.val) hb
  have hab : a=b := Fin.ext hlevel
  subst b
  have hij : i=j := Fin.ext hs
  subst j
  have huv : u=v := Fin.ext (congrArg (fun x : Bath d k L => x.2.val) hb)
  subst v
  rfl
lemma destinationColumn_injective (d k L : ℕ) (hkd : k ≤ d) :
    Function.Injective (destinationColumn d k L hkd) := by
  rintro ⟨a,i,u⟩ ⟨b,j,v⟩ he
  have hs:=congrArg (fun x : Hardware d k L => x.1.val) he
  have hb:=(Fintype.equivFin (Bath d k L)).injective (congrArg (fun x : Hardware d k L => x.2.2) he)
  have hlevel:=congrArg (fun x : Bath d k L => x.1.val) hb
  have hab : a=b := Fin.ext (by change a.val+1=b.val+1 at hlevel; omega)
  subst b
  have hij : i=j := Fin.ext hs
  subst j
  have huv : u=v := Fin.ext (congrArg (fun x : Bath d k L => x.2.val) hb)
  subst v
  rfl
lemma finalColumn_injective (d k L : ℕ) (hkd : k ≤ d) : Function.Injective (finalColumn d k L hkd) :=
  (destinationColumn_injective d k L hkd).comp (transfer d k L).injective
lemma columns_disjoint (d k L : ℕ) (hkd : k ≤ d) (x y : Columns d k L) :
    initialColumn d k L x ≠ finalColumn d k L hkd y := by
  intro h
  have he:=congrArg (fun z : Hardware d k L => z.2.1.val) h
  change (0:ℕ)=1 at he
  omega

def totalEnergy (β : ℝ) (d k L : ℕ) (x : Hardware d k L) : ℝ :=
  (if x.2.1=0 then 0 else -gap β d k) + bathEnergy β d k L x.2.2
lemma initial_energy (β : ℝ) (d k L : ℕ) (x : Columns d k L) :
    totalEnergy β d k L (initialColumn d k L x) = gap β d k*x.1.val := by
  simp [totalEnergy,initialColumn,bathEnergy]
lemma final_energy (β : ℝ) (d k L : ℕ) (hkd : k ≤ d) (x : Columns d k L) :
    totalEnergy β d k L (finalColumn d k L hkd x) = gap β d k*x.1.val := by
  simp only [totalEnergy,finalColumn,destinationColumn,bathEnergy,Equiv.symm_apply_apply]
  change (if (1:Fin 2)=0 then 0 else -gap β d k)+gap β d k*((x.1.val+1:ℕ):ℝ)=_
  norm_num
  ring

def ladderPermutation (d k L : ℕ) (hkd : k ≤ d) : Equiv.Perm (Hardware d k L) :=
  FiniteSwap.permutation (initialColumn d k L) (finalColumn d k L hkd)
    (initialColumn_injective d k L) (finalColumn_injective d k L hkd) (columns_disjoint d k L hkd)
def cappedColumn (d k L : ℕ) (i : Fin d) (r : Fin (multiplicity d k L L)) : Hardware d k L :=
  (i,0,Fintype.equivFin (Bath d k L) ⟨Fin.last L,r⟩)
lemma cappedColumn_fixed (d k L : ℕ) (hkd : k ≤ d) (i : Fin d) (r : Fin (multiplicity d k L L)) :
    ladderPermutation d k L hkd (cappedColumn d k L i r) = cappedColumn d k L i r := by
  change FiniteSwap.apply (initialColumn d k L) (finalColumn d k L hkd) _ = _
  apply FiniteSwap.outside
  · rintro ⟨x,hx⟩
    have hb := (Fintype.equivFin (Bath d k L)).injective (congrArg (fun z : Hardware d k L => z.2.2) hx)
    have hl := congrArg (fun b : Bath d k L => b.1.val) hb
    change x.1.val=L at hl
    exact (Nat.ne_of_lt x.1.isLt) hl
  · rintro ⟨y,hy⟩
    have hb := congrArg (fun z : Hardware d k L => z.2.1.val) hy
    change (1 : ℕ)=0 at hb
    omega
lemma destinationColumn_swapped (d k L : ℕ) (hkd : k ≤ d) (y : Targets d k L) :
    ladderPermutation d k L hkd (destinationColumn d k L hkd y) =
      initialColumn d k L ((transfer d k L).symm y) := by
  have he : finalColumn d k L hkd ((transfer d k L).symm y) = destinationColumn d k L hkd y := by
    exact congrArg (destinationColumn d k L hkd) ((transfer d k L).apply_symm_apply y)
  rw [←he]
  exact FiniteSwap.on_target _ _ (finalColumn_injective d k L hkd) (columns_disjoint d k L hkd) _
lemma outside_rank_fixed (d k L : ℕ) (hkd : k ≤ d) (i : Fin d) (hi : k ≤ i.val)
    (r : Fin (bathSize d k L)) : ladderPermutation d k L hkd (i,1,r) = (i,1,r) := by
  change FiniteSwap.apply (initialColumn d k L) (finalColumn d k L hkd) _ = _
  apply FiniteSwap.outside
  · rintro ⟨x,hx⟩
    have hb := congrArg (fun z : Hardware d k L => z.2.1.val) hx
    change (0 : ℕ)=1 at hb
    omega
  · rintro ⟨y,hy⟩
    have hv := congrArg (fun z : Hardware d k L => z.1.val) hy
    have hk : (finalColumn d k L hkd y).1.val<k := (transfer d k L y).2.1.isLt
    change (finalColumn d k L hkd y).1.val=i.val at hv
    omega

lemma ladderPermutation_unitary (d k L : ℕ) (hkd : k ≤ d) :
    IsUnitary ((ladderPermutation d k L hkd).permMatrix ℂ) := Recorder.permutation_unitary _
lemma ladderPermutation_conserves (β : ℝ) (d k L : ℕ) (hkd : k ≤ d) :
    Conserves ((ladderPermutation d k L hkd).permMatrix ℂ)
      (diagonal (fun x => (totalEnergy β d k L x : ℂ))) := by
  apply FiniteSwap.conserves
  intro x
  rw [initial_energy,final_energy]

lemma totalHamiltonian (β : ℝ) (d k L : ℕ) :
    converterHamiltonian (zeroHamiltonian d) (bathHamiltonian β d k L) (-gap β d k) =
      diagonal (fun x => (totalEnergy β d k L x : ℂ)) := by
  ext ⟨i,b,r⟩ ⟨j,c,u⟩
  fin_cases b <;> fin_cases c <;> by_cases hij : i=j <;> by_cases hru : r=u <;>
    simp_all [converterHamiltonian,zeroHamiltonian,bathHamiltonian,totalEnergy,
      Matrix.kroneckerMap_apply,Matrix.of_apply,Matrix.diagonal]

def constructedLadder (β : ℝ) (d k L : ℕ) (hkd : k ≤ d) : Ladder β d k L where
  U := (ladderPermutation d k L hkd).permMatrix ℂ
  unitary := ladderPermutation_unitary d k L hkd
  conserves := by
    rw [totalHamiltonian]
    exact ladderPermutation_conserves β d k L hkd

end ScheduleLaw.Blueprint.FiniteFlat
