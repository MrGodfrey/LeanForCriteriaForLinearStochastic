module

public import LinearStochastic.RawControlProperties
public import LinearStochastic.BrownianControlClassification
public import LinearStochastic.MatrixApproximateClassification

@[expose] public section

/-! The paper's ordinary progressive-control, raw continuous-S²-solution
AC and ANC are exactly the algebraic terminal flag test. -/
noncomputable section
namespace LinearStochastic.RawBrownianClassification
open MeasureTheory ProbabilityTheory
open scoped NNReal
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)

include c in
/-- Every positive horizon has the classification for actual ordinary
progressive controls and original raw continuous S² solutions. -/
theorem classification (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    (RawControlProperties.Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b hW hWm T A B C D ↔
      (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥) ∧
    (RawControlProperties.ApproximateNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b hW hWm T A B C D ↔
      (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  have h := BrownianControlClassification.classification b c hW hWm hInd i₀ T hT A B C D
  exact ⟨(RawControlProperties.approximate_iff b c hW hWm T A B C D i₀).trans h.1,
    (RawControlProperties.approximateNull_iff b c hW hWm T A B C D i₀).trans h.2⟩

/-- Literal real-matrix specialization, including the same n-step transpose
flag as the manuscript, for actual ordinary-progressive/raw-S² controls. -/
theorem matrix_classification {n r m : ℕ} {W : Fin m → ℝ≥0 → Ω → ℝ}
    (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
    (hInd : iIndepFun (fun i ω t => W i t ω) μ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    (RawControlProperties.Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (ZeroObservationMatrices.matrixMap A)
      (ZeroObservationMatrices.matrixMap B) (fun i => ZeroObservationMatrices.matrixMap (C i))
      (fun i => ZeroObservationMatrices.matrixMap (D i)) ↔ (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) ∧
    (RawControlProperties.ApproximateNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (ZeroObservationMatrices.matrixMap A)
      (ZeroObservationMatrices.matrixMap B) (fun i => ZeroObservationMatrices.matrixMap (C i))
      (fun i => ZeroObservationMatrices.matrixMap (D i)) ↔ (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  have h := classification (EuclideanSpace.basisFun (Fin n) ℝ) (EuclideanSpace.basisFun (Fin r) ℝ)
    hW hWm hInd ⟨0,hm⟩ T hT (ZeroObservationMatrices.matrixMap A) (ZeroObservationMatrices.matrixMap B)
      (fun i => ZeroObservationMatrices.matrixMap (C i)) (fun i => ZeroObservationMatrices.matrixMap (D i))
  simp only [finrank_euclideanSpace_fin] at h
  exact ⟨h.1.trans (ZeroObservationMatrices.matrix_flag_bot_iff A B C D n).symm,
    h.2.trans (ZeroObservationMatrices.matrix_flag_bot_iff A B C D n).symm⟩

end LinearStochastic.RawBrownianClassification
