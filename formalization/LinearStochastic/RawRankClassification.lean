module

public import LinearStochastic.RawBrownianClassification

@[expose] public section

/-! Literal finite block-matrix rank criteria for ordinary progressive
controls and actual raw continuous S² solutions. -/
noncomputable section
namespace LinearStochastic.RawRankClassification
open MeasureTheory ProbabilityTheory
open scoped NNReal
open ZeroObservationMatrices RawControlProperties
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] {n r m : ℕ}
  {W : Fin m → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)

/-- Both ordinary-progressive AC and ANC are exactly the paper's literal
rank[N_n K_n]−rank N_n=n test, at every prescribed positive horizon. -/
theorem classification (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    (Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) (EuclideanSpace.basisFun (Fin n) ℝ)
      hW hWm T (matrixMap A) (matrixMap B) (fun i => matrixMap (C i)) (fun i => matrixMap (D i)) ↔
      (Matrix.fromCols (Coordinates.finitePair A B C D (n-1)).2
        (Coordinates.finitePair A B C D (n-1)).1).rank -
        (Coordinates.finitePair A B C D (n-1)).2.rank = n) ∧
    (ApproximateNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) (EuclideanSpace.basisFun (Fin n) ℝ)
      hW hWm T (matrixMap A) (matrixMap B) (fun i => matrixMap (C i)) (fun i => matrixMap (D i)) ↔
      (Matrix.fromCols (Coordinates.finitePair A B C D (n-1)).2
        (Coordinates.finitePair A B C D (n-1)).1).rank -
        (Coordinates.finitePair A B C D (n-1)).2.rank = n) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  have h := RawBrownianClassification.matrix_classification hW hWm hInd hm T hT A B C D
  exact ⟨h.1.trans (MatrixApproximateClassification.flag_iff_rank hn A B C D),
    h.2.trans (MatrixApproximateClassification.flag_iff_rank hn A B C D)⟩

end LinearStochastic.RawRankClassification
