module

public import LinearStochastic.RawCompleteClassification

@[expose] public section

/-! The complete finite-rank corollary and reduced finite-word exact-control
criterion, for the actual original-coefficient stochastic system. -/
noncomputable section
namespace LinearStochastic.RawRankCriteria
open MeasureTheory ProbabilityTheory
open scoped NNReal
open ZeroObservationMatrices
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] {n r m : ℕ}
  {W : Fin m → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t=>W i t ω) μ)

/-- The paper's δ_n uses the literal finite recursive matrices in their
proved original-coordinate order. -/
def rankDifference (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) : ℕ :=
  (Matrix.fromCols (Coordinates.finitePair A B C D (n-1)).2
    (Coordinates.finitePair A B C D (n-1)).1).rank-
    (Coordinates.finitePair A B C D (n-1)).2.rank

/-- AC, ANC and ENC have exactly the same literal rank-difference test. -/
theorem null_rank (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    (RawControlProperties.Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ↔ rankDifference A B C D=n) ∧
    (RawControlProperties.ApproximateNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ↔ rankDifference A B C D=n) ∧
    (RawExactProperties.ExactNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ↔ rankDifference A B C D=n) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  have h := RawRankClassification.classification hW hWm hInd hn hm T hT A B C D
  exact ⟨h.1,h.2,(RawCompleteClassification.exactNull_iff_flag hW hWm hInd hn hm T hT A B C D).trans
    (MatrixApproximateClassification.flag_iff_rank hn A B C D)⟩

/-- EC requires and suffices for the two original-coefficient rank tests. -/
theorem exact_rank (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    RawExactProperties.Exact (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ↔
      rankDifference A B C D=n ∧ (SurjectiveMatrices.stack D).rank=m*n := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  exact (RawCompleteClassification.exact_iff_flag_rank hW hWm hInd hn hm T hT A B C D).trans
    (and_congr (MatrixApproximateClassification.flag_iff_rank hn A B C D) Iff.rfl)

/-- Under full joint diffusion rank, the actual EC property is exactly the
finite-word rank condition built from the canonical J, H, E_i and F. -/
theorem exact_word_rank (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hD : (SurjectiveMatrices.stack D).rank=m*n) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    RawExactProperties.Exact (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ↔
      (WordMatrices.cumulativeMatrix (SurjectiveMatrices.reducedGenerators A B C D hD)
        (SurjectiveMatrices.reducedH B D hD) (n-1)).rank=n := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  have h := RawCompleteClassification.exact_iff_flag_rank hW hWm hInd hn hm T hT A B C D
  rw [and_iff_left hD] at h
  exact h.trans ((matrix_flag_bot_iff A B C D n).trans
    (SurjectiveMatrices.flag_bot_iff_word_matrix_full_rank A B C D hD))

end LinearStochastic.RawRankCriteria
