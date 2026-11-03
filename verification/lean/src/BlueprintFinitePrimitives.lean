import FiniteFlatBlueprint
import SupportConversion

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Matrix Filter
open scoped BigOperators Kronecker ComplexOrder Topology Matrix.Norms.L2Operator
namespace ScheduleLaw.Blueprint
open History

theorem energy_shell_support_conversion {d : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (H : Hamiltonian (Fin d)) (P Q : Mat (Fin d))
    (hP : P.IsHermitian) (hPi : P*P=P) (hQ : Q.IsHermitian) (hQi : Q*Q=Q)
    (hPH : P*H.matrix=H.matrix*P) (hQH : Q*H.matrix=H.matrix*Q)
    (hZP : 0 < energy P (boltzmann β H)) (hZQ : 0 < energy Q (boltzmann β H))
    (x f : ℝ) (hx : x < Real.log (energy Q (boltzmann β H)/energy P (boltzmann β H))/β)
    (hf : 0 < f) :
    ∃ C : SupportConverter β H x, ∀ z (ρ : Density (Fin d × Fin z)),
      (P ⊗ₖ (1 : Mat (Fin z)))*ρ.matrix=ρ.matrix →
      1-f ≤ energy ((Q ⊗ₖ (pureMatrix (fun j : Fin 2 => if j=1 then 1 else 0) ⊗ₖ
        (1 : Mat (Fin C.r)))) ⊗ₖ (1 : Mat (Fin z))) (C.run z ρ.matrix) := by
  exact SupportConversion.convert hd β hβ H P Q hP hPi hQ hQi hPH hQH hZP hZQ x f hx hf

/-- The equal-degeneracy flat case attains the exact finite debit, whereas
the all-state support converter above uses a strict work inequality. -/
theorem exact_flat_rank_conversion {d : ℕ} (hd : 0 < d) (β : ℝ) (hβ : 0 < β)
    (Q : Mat (Fin d)) (hQ : Q.IsHermitian) (hQi : Q*Q=Q)
    (k : ℕ) (hk : 0 < k) (hkd : k ≤ d) (htr : Q.trace=(k : ℂ)) (f : ℝ) (hf : 0 < f) :
    ∃ C : SupportConverter β (⟨0,by simp⟩ : Hamiltonian (Fin d)) (-Real.log ((d : ℝ)/k)/β),
      ∃ p : ℝ, 1-f ≤ p ∧ p ≤ 1 ∧
        partialRight (partialRight ((
          ((1 : Mat (Fin d)) ⊗ₖ (pureMatrix (fun j : Fin 2 => if j=1 then 1 else 0) ⊗ₖ
            (1 : Mat (Fin C.r)))) ⊗ₖ (1 : Mat (Fin 1))) *
          C.run 1 ((((d : ℂ)⁻¹) • (1 : Mat (Fin d))) ⊗ₖ (1 : Mat (Fin 1))))) =
            (((p/(k : ℝ) : ℝ) : ℂ) • Q) := by
  exact FiniteFlat.exact_flat hd β hβ Q hQ hQi k hk hkd htr f hf

def shellSwap {d : ℕ} (P Q V : Mat (Fin d)) : Mat (Fin d) := V+Vᴴ+(1-P-Q)

theorem finite_shell_swap_completion {d : ℕ} (P Q V H : Mat (Fin d))
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (hH : H.IsHermitian)
    (hPi : P*P=P) (hQi : Q*Q=Q) (hPQ : P*Q=0)
    (hVP : V*P=V) (hQV : Q*V=V) (hVV : Vᴴ*V=P) (hVV' : V*Vᴴ=Q)
    (hPH : P*H=H*P) (hQH : Q*H=H*Q) (hVH : V*H=H*V) :
    IsUnitary (shellSwap P Q V) ∧ Conserves (shellSwap P Q V) H ∧
      shellSwap P Q V*P=V ∧ shellSwap P Q V*(1-P-Q)=1-P-Q := by
  have hQP : Q*P=0 := by
    have h := congrArg Matrix.conjTranspose hPQ
    simpa only [conjTranspose_mul, hP.eq, hQ.eq, conjTranspose_zero] using h
  have hPV : P*V=0 := by
    calc P*V = P*(Q*V) := by rw [hQV]
         _ = 0 := by rw [← mul_assoc,hPQ,zero_mul]
  have hVQ : V*Q=0 := by
    calc V*Q = (V*P)*Q := by rw [hVP]
         _ = 0 := by rw [mul_assoc,hPQ,mul_zero]
  have hPVt : P*Vᴴ=Vᴴ := by
    have h := congrArg Matrix.conjTranspose hVP
    simpa only [conjTranspose_mul,hP.eq] using h
  have hVtQ : Vᴴ*Q=Vᴴ := by
    have h := congrArg Matrix.conjTranspose hQV
    simpa only [conjTranspose_mul,hQ.eq] using h
  have hVtP : Vᴴ*P=0 := by
    have h := congrArg Matrix.conjTranspose hPV
    simpa only [conjTranspose_mul,hP.eq,conjTranspose_zero] using h
  have hQVt : Q*Vᴴ=0 := by
    have h := congrArg Matrix.conjTranspose hVQ
    simpa only [conjTranspose_mul,hQ.eq,conjTranspose_zero] using h
  have hV2 : V*V=0 := by
    calc V*V = V*(Q*V) := by rw [hQV]
         _ = 0 := by rw [← mul_assoc,hVQ,zero_mul]
  have hVt2 : Vᴴ*Vᴴ=0 := by
    have h := congrArg Matrix.conjTranspose hV2
    simpa only [conjTranspose_mul,conjTranspose_zero] using h
  have hR2 : (1-P-Q)*(1-P-Q)=1-P-Q := by
    simp only [sub_mul,mul_sub,one_mul,mul_one,hPi,hQi,hPQ,hQP]
    abel
  have hVR : V*(1-P-Q)=0 := by
    simp [mul_sub,hVP,hVQ]
  have hVtR : Vᴴ*(1-P-Q)=0 := by
    simp [mul_sub,hVtP,hVtQ]
  have hRV : (1-P-Q)*V=0 := by
    simp [sub_mul,hPV,hQV]
  have hRVt : (1-P-Q)*Vᴴ=0 := by
    simp [sub_mul,hPVt,hQVt]
  have hstar : (shellSwap P Q V)ᴴ=shellSwap P Q V := by
    simp only [shellSwap,conjTranspose_add,conjTranspose_sub,conjTranspose_one,
      conjTranspose_conjTranspose,hP.eq,hQ.eq]
    abel
  have hU2 : shellSwap P Q V*shellSwap P Q V=1 := by
    simp only [shellSwap,add_mul,mul_add,hV2,hVt2,hVV,hVV',hVR,hVtR,hRV,hRVt,hR2]
    abel
  have hunit : IsUnitary (shellSwap P Q V) := by
    constructor <;> rw [hstar] <;> exact hU2
  have hVtH : Vᴴ*H=H*Vᴴ := by
    have h := congrArg Matrix.conjTranspose hVH
    simpa only [conjTranspose_mul,hH.eq] using h.symm
  have hcomm : shellSwap P Q V*H=H*shellSwap P Q V := by
    simp only [shellSwap,add_mul,mul_add,sub_mul,mul_sub,one_mul,mul_one]
    rw [hVH,hVtH,hPH,hQH]
  refine ⟨hunit,?_,?_,?_⟩
  · unfold Conserves
    rw [mul_assoc,← hcomm,← mul_assoc,hunit.1,one_mul]
  · simp only [shellSwap,add_mul,sub_mul,one_mul,hVP,hVtP,hPi,hQP]
    abel
  · simp only [shellSwap,add_mul,hVR,hVtR,hR2,zero_add]

def sinePacket (L : ℕ) (x : ℤ) : ℂ :=
  if 0 ≤ x ∧ x < L then (Real.sqrt (2/(L+1 : ℝ))*Real.sin (Real.pi*(x+1)/(L+1 : ℝ)) : ℝ) else 0

theorem sine_packet_normalized (L : ℕ) (hL : 0 < L) :
    (∑' x : ℤ, Complex.normSq (sinePacket L x))=1 := by
  have he (x : ℤ) : sinePacket L x = (W2.sineValue L x : ℂ) := by
    unfold sinePacket W2.sineValue
    split_ifs <;> rfl
  simp_rw [he,Complex.normSq_ofReal,← sq]
  exact W2.sineValue_normalized L hL

theorem sine_packet_shift_bound (L : ℕ) (hL : 0 < L) (k : ℤ) :
    (∑' x : ℤ, Complex.normSq (sinePacket L (x-k)-sinePacket L x)) ≤
      (Real.pi*(|k| : ℤ)/(L+1 : ℝ))^2 := by
  have he (x : ℤ) : sinePacket L x = (W2.sineValue L x : ℂ) := by
    unfold sinePacket W2.sineValue
    split_ifs <;> rfl
  simp_rw [he,← Complex.ofReal_sub,Complex.normSq_ofReal,← sq]
  exact W2.sineValue_shift_bound L hL k

end ScheduleLaw.Blueprint
