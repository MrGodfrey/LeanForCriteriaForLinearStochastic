module

public import LinearStochastic.SwitchingRates
public import LinearStochastic.PolynomialFeedbackGrowth

@[expose] public section

/-! Countably many actual feasible matrix feedbacks chosen at the concrete
switching rates. A single polynomial bound and switching constant work for
all intervals and for every initial state. -/
noncomputable section
namespace LinearStochastic.SwitchingFeedbackFamily
open scoped Matrix.Norms.Frobenius
open MatrixGrowthBounds SwitchingRates
variable {n r m : ℕ} [Nonempty (Fin n)]

structure Family (T : ℝ)
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
  P : ℕ → Matrix (Fin n) (Fin n) ℝ
  U : ℕ → Matrix (Fin r) (Fin n) ℝ
  positive : ∀ j, (P j).PosDef
  feasible : ∀ j, (-LMIMatrixCoordinates.matrixLMI A B C D (rate L T j) (P j) (U j)).PosDef
  condition : ∀ j, conditionNumber (P j) (positive j).isHermitian ≤ M*(rate L T j)^p
  gain : ∀ j, ‖(U j*(P j)⁻¹).toEuclideanLin.toContinuousLinearMap‖^2 ≤ M*(rate L T j)^p

theorem exists_family (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) :
    Nonempty (Family T A B C D) := by
  obtain ⟨M,hM,p,hp,hpoly⟩ := PolynomialFeedbackGrowth.zero_flag_polynomial_feedback A B C D hm hflag
  obtain ⟨L,hL,hLp,hsmall⟩ := Switching.exists_switching_constant M p
  have hfamily (j : ℕ) := hpoly (rate L T j) (rate_ge_one L T hL hT hT1 j)
  choose P U hP hneg hcond hgain using hfamily
  exact ⟨⟨M,hM,p,hp,L,hL,hLp,hsmall,P,U,hP,hneg,hcond,hgain⟩⟩

theorem uniform_contraction (T : ℝ) (hT : 0 < T) (hT1 : T ≤ 1)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (q : Family T A B C D) (j : ℕ) :
    (4:ℝ)^(2*q.p)*q.M*(rate q.L T j)^q.p*Real.exp (-rate q.L T j*length T j) ≤ 1/2 :=
  contraction_factor q.L T q.M q.p (zero_le_one.trans q.M_ge_one) q.L_ge_one q.L_ge_four_p
    q.small hT hT1 j

end LinearStochastic.SwitchingFeedbackFamily
