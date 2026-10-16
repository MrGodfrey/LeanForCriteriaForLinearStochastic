import LinearStochastic.SwitchingFeedbackFamily

/-! One coefficient-dependent parameter choice works for every short horizon,
so the quantitative null-control cost has genuinely uniform constants. -/
noncomputable section
namespace LinearStochastic.UniformSwitchingFamily
open MatrixGrowthBounds SwitchingRates SwitchingFeedbackFamily
variable {n r m : ℕ} [Nonempty (Fin n)]

structure Parameters
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) where
  M : ℝ
  M_ge_one : 1 ≤ M
  p : ℕ
  p_ge_one : 1 ≤ p
  L : ℝ
  L_ge_one : 1 ≤ L
  L_ge_four_p : 4*(p:ℝ) ≤ L
  small : (4:ℝ)^(2*p)*M*L^p*Real.exp (-L/2) ≤ 1/2
  feedback : ∀ ρ : ℝ, 1 ≤ ρ → ∃ (P : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin r) (Fin n) ℝ) (hP : P.PosDef),
    (-LMIMatrixCoordinates.matrixLMI A B C D ρ P U).PosDef ∧
    conditionNumber P hP.isHermitian ≤ M*ρ^p ∧
    ‖(U*P⁻¹).toEuclideanLin.toContinuousLinearMap‖^2 ≤ M*ρ^p

theorem exists_parameters (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) :
    Nonempty (Parameters A B C D) := by
  obtain ⟨M,hM,p,hp,hpoly⟩ := PolynomialFeedbackGrowth.zero_flag_polynomial_feedback A B C D hm hflag
  obtain ⟨L,hL,hLp,hsmall⟩ := Switching.exists_switching_constant M p
  exact ⟨⟨M,hM,p,hp,L,hL,hLp,hsmall,hpoly⟩⟩

variable (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
  (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)

def family (q : Parameters A B C D) (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) : Family T A B C D := by
  have hfamily (j : ℕ) := q.feedback (rate q.L T j) (rate_ge_one q.L T q.L_ge_one hT hT1 j)
  choose P U hP hneg hcond hgain using hfamily
  exact ⟨q.M,q.M_ge_one,q.p,q.p_ge_one,q.L,q.L_ge_one,q.L_ge_four_p,q.small,P,U,hP,hneg,hcond,hgain⟩

theorem family_M (q : Parameters A B C D) (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) :
    (family A B C D q T hT hT1).M = q.M := rfl

theorem family_p (q : Parameters A B C D) (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) :
    (family A B C D q T hT hT1).p = q.p := rfl

theorem family_L (q : Parameters A B C D) (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) :
    (family A B C D q T hT hT1).L = q.L := rfl

end LinearStochastic.UniformSwitchingFamily
