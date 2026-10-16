import LinearStochastic.BrownianControlClassification
import LinearStochastic.ZeroObservationMatrices

/-! The actual original Brownian control system with literal real matrices:
AC and ANC are exactly the manuscript flag and block-matrix rank tests. -/
noncomputable section
namespace LinearStochastic.MatrixApproximateClassification
open MeasureTheory ProbabilityTheory
open scoped NNReal
open ZeroObservationMatrices ActualControlProperties

/-- The actual recursively built K_n,N_n matrix test is precisely V_n=0. -/
theorem flag_iff_rank {n r m : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥ ↔
      (Matrix.fromCols (Coordinates.finitePair A B C D (n-1)).2
        (Coordinates.finitePair A B C D (n-1)).1).rank -
        (Coordinates.finitePair A B C D (n-1)).2.rank = n := by
  rw [Coordinates.finitePair_rank_codimension]
  have hn' : n-1+1=n := by omega
  rw [hn',←Submodule.finrank_eq_zero]
  omega

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] {n r m : ℕ}
  {W : Fin m → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)

/-- Every positive prescribed horizon has the literal matrix AC/ANC flag
classification, with no representation, local-rate or continuity premise. -/
theorem classification (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    (Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) (EuclideanSpace.basisFun (Fin n) ℝ)
      (fun i => (hW i).toIsPreBrownianReal) hWm T (matrixMap A) (matrixMap B)
      (fun i => matrixMap (C i)) (fun i => matrixMap (D i)) ↔
        (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) ∧
    (ApproximateNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) (EuclideanSpace.basisFun (Fin n) ℝ)
      (fun i => (hW i).toIsPreBrownianReal) hWm T (matrixMap A) (matrixMap B)
      (fun i => matrixMap (C i)) (fun i => matrixMap (D i)) ↔
        (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  have h := BrownianControlClassification.classification (EuclideanSpace.basisFun (Fin n) ℝ)
    (EuclideanSpace.basisFun (Fin r) ℝ) hW hWm hInd ⟨0,hm⟩ T hT
    (matrixMap A) (matrixMap B) (fun i => matrixMap (C i)) (fun i => matrixMap (D i))
  simp only [finrank_euclideanSpace_fin] at h
  exact ⟨h.1.trans (matrix_flag_bot_iff A B C D n).symm,
    h.2.trans (matrix_flag_bot_iff A B C D n).symm⟩

/-- The manuscript's literal finite rank difference is the actual AC test. -/
theorem approximate_iff_rank (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) (EuclideanSpace.basisFun (Fin n) ℝ)
      (fun i => (hW i).toIsPreBrownianReal) hWm T (matrixMap A) (matrixMap B)
      (fun i => matrixMap (C i)) (fun i => matrixMap (D i)) ↔
      (Matrix.fromCols (Coordinates.finitePair A B C D (n-1)).2
        (Coordinates.finitePair A B C D (n-1)).1).rank -
        (Coordinates.finitePair A B C D (n-1)).2.rank = n := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  exact (classification hW hWm hInd hm T hT A B C D).1.trans (flag_iff_rank hn A B C D)

end LinearStochastic.MatrixApproximateClassification
