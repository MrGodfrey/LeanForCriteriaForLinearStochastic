module

public import LinearStochastic.SemialgebraicMinimum
public import LinearStochastic.MatrixGrowthBounds

@[expose] public section

noncomputable section
namespace LinearStochastic.PolynomialFeedbackGrowth
open scoped Matrix.Norms.Frobenius
open MatrixNormalization MatrixGrowthBounds QuadraticMinimum SemialgebraicCoordinates
variable {n r m : ℕ} [Nonempty (Fin n)]
variable (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)

/-- Genuine polynomial bounds for normalized feasible pairs at every rate.
The minimum's existence, continuity, semialgebraicity and growth are all proved. -/
theorem normalized_polynomial_feedback (i : Fin m)
    (hfeas : ∀ ρ : Set.Ici (1 : ℝ), ∃ P K, Feasible A B C D ρ P K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∃ p : ℕ, 1 ≤ p ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      ∃ P K, ∃ hP : P.PosDef, Feasible A B C D ρ P K ∧
        conditionNumber P hP.isHermitian ≤ M*ρ^p ∧
        ‖(K*P⁻¹).toEuclideanLin.toContinuousLinearMap‖^2 ≤ M*ρ^p := by
  obtain ⟨M,hM,p,hp,hbound⟩ := continuous_semialgebraic_growth
    (MatrixValue.valueReal A B C D hfeas)
    (MatrixValue.valueReal_continuousOn A B C D hfeas)
    (SemialgebraicMinimum.isSemialgebraic_minimum_graph A B C D hfeas)
  refine ⟨M,hM,p,hp,?_⟩
  intro ρ hρ
  obtain ⟨P,K,hf,hg,_⟩ := (MatrixValue.value_eq_iff A B C D hfeas ⟨ρ,hρ⟩
    (MatrixValue.value A B C D hfeas ⟨ρ,hρ⟩)).mp rfl
  have hP := feasible_posDef A B C D ρ P K hf i
  have hobj : matrixObjective (P,K) ≤ M*ρ^p := by
    rw [hg,←MatrixValue.valueReal_on_ray A B C D hfeas ρ hρ]
    exact (le_abs_self _).trans (hbound ρ hρ)
  refine ⟨P,K,hP,hf,?_,(feasible_gain_bound A B C D ρ P K hf i).trans hobj⟩
  exact (conditionNumber_le_objective P K hP.isHermitian (feasible_ge_one A B C D ρ P K hf i)).trans hobj

/-- The manuscript's full feedback-growth lemma, starting from the actual
strict LMI feasibility at every rate and ending with the actual spectral
condition number and Euclidean norm of the literal gain K P⁻¹. -/
theorem polynomial_feedback (hm : 0 < m)
    (hfeas : ∀ ρ : ℝ, 1 ≤ ρ → ∃ P K, P.IsSymm ∧
      (-LMIMatrixCoordinates.matrixLMI A B C D ρ P K).PosDef) :
    ∃ M : ℝ, 1 ≤ M ∧ ∃ p : ℕ, 1 ≤ p ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      ∃ P K, ∃ hP : P.PosDef, (-LMIMatrixCoordinates.matrixLMI A B C D ρ P K).PosDef ∧
        conditionNumber P hP.isHermitian ≤ M*ρ^p ∧
        ‖(K*P⁻¹).toEuclideanLin.toContinuousLinearMap‖^2 ≤ M*ρ^p := by
  have hn : ∀ ρ : Set.Ici (1 : ℝ), ∃ P K, Feasible A B C D ρ P K := by
    intro ρ
    obtain ⟨P,K,hs,hp⟩ := hfeas ρ ρ.property
    obtain ⟨c,_,hc⟩ := normalize_strict A B C D ρ P K hs hp
    exact ⟨c•P,c•K,hc⟩
  obtain ⟨M,hM,p,hp,h⟩ := normalized_polynomial_feedback A B C D ⟨0,hm⟩ hn
  refine ⟨M,hM,p,hp,?_⟩
  intro ρ hρ
  obtain ⟨P,K,hP,hf,hc,hg⟩ := h ρ hρ
  exact ⟨P,K,hP,feasible_strict_lmi A B C D ρ P K hf,hc,hg⟩

/-- Original coefficient flag vanishing supplies the hypothesis, so polynomially
bounded feedbacks are obtained from the paper's own algebraic criterion. -/
theorem zero_flag_polynomial_feedback (hm : 0 < m)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) :
    ∃ M : ℝ, 1 ≤ M ∧ ∃ p : ℕ, 1 ≤ p ∧ ∀ ρ : ℝ, 1 ≤ ρ →
      ∃ P K, ∃ hP : P.PosDef, (-LMIMatrixCoordinates.matrixLMI A B C D ρ P K).PosDef ∧
        conditionNumber P hP.isHermitian ≤ M*ρ^p ∧
        ‖(K*P⁻¹).toEuclideanLin.toContinuousLinearMap‖^2 ≤ M*ρ^p :=
  polynomial_feedback A B C D hm
    (fun ρ _ => LMIMatrixCoordinates.arbitrary_rate_matrix_feasible A B C D hflag ρ)

end LinearStochastic.PolynomialFeedbackGrowth
