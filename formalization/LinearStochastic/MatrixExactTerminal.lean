import LinearStochastic.RawExactProperties
import LinearStochastic.BrownianExactTerminal
import LinearStochastic.AlgebraSurjectiveMatrices
import LinearStochastic.ZeroObservationMatrices

/-! Surjective diffusion gives exact-terminal controllability for original
ordinary-progressive controls; the finite real-matrix statement uses literally
the rank of the vertically stacked diffusion-control matrix. -/
noncomputable section
namespace LinearStochastic.MatrixExactTerminal
open MeasureTheory ProbabilityTheory
open scoped NNReal
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)

include c in
/-- The exact-terminal witness includes a genuine raw continuous S² path and
an ordinary progressive finite-energy control on the original probability space. -/
theorem raw_exact_terminal (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion (fun i => (D i).toLinearMap))) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    RawExactProperties.ExactTerminal (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b hW hWm T A B C D := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  exact (RawExactProperties.exactTerminal_iff b c hW hWm T A B C D i₀).mpr
    (BrownianExactTerminal.exact_terminal b hW hWm hInd i₀ T hT A B C D hD)

include c in
/-- The raw-path EC sufficiency direction, keeping its ENC premise explicit
until the separate switching construction supplies it. -/
theorem raw_exact_of_exactNull (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion (fun i => (D i).toLinearMap))) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    RawExactProperties.ExactNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b hW hWm T A B C D →
    RawExactProperties.Exact (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b hW hWm T A B C D := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  intro hn
  exact (RawExactProperties.exact_iff_terminal_and_null b c hW hWm T A B C D i₀).mpr
    ⟨raw_exact_terminal b c hW hWm hInd i₀ T hT A B C D hD,hn⟩

/-- Literal stacked-matrix full row rank supplies the exact-terminal property
for all actual F_T-measurable square-integrable random vector targets. -/
theorem matrix_exact_terminal {n r m : ℕ} {W : Fin m → ℝ≥0 → Ω → ℝ}
    (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
    (hInd : iIndepFun (fun i ω t => W i t ω) μ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hD : (SurjectiveMatrices.stack D).rank = m*n) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    RawExactProperties.ExactTerminal (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (ZeroObservationMatrices.matrixMap A)
      (ZeroObservationMatrices.matrixMap B) (fun i => ZeroObservationMatrices.matrixMap (C i))
      (fun i => ZeroObservationMatrices.matrixMap (D i)) := by
  exact raw_exact_terminal (EuclideanSpace.basisFun (Fin n) ℝ) (EuclideanSpace.basisFun (Fin r) ℝ)
    hW hWm hInd ⟨0,hm⟩ T hT (ZeroObservationMatrices.matrixMap A) (ZeroObservationMatrices.matrixMap B)
      (fun i => ZeroObservationMatrices.matrixMap (C i)) (fun i => ZeroObservationMatrices.matrixMap (D i))
      ((SurjectiveMatrices.stack_full_rank_iff D).mp hD)

/-- Literal full stacked diffusion rank plus raw ENC implies raw EC at each
prescribed positive horizon; no uniform-energy or closure assertion is used. -/
theorem matrix_exact_of_exactNull {n r m : ℕ} {W : Fin m → ℝ≥0 → Ω → ℝ}
    (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
    (hInd : iIndepFun (fun i ω t => W i t ω) μ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hD : (SurjectiveMatrices.stack D).rank = m*n) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    RawExactProperties.ExactNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (ZeroObservationMatrices.matrixMap A)
      (ZeroObservationMatrices.matrixMap B) (fun i => ZeroObservationMatrices.matrixMap (C i))
      (fun i => ZeroObservationMatrices.matrixMap (D i)) →
    RawExactProperties.Exact (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (ZeroObservationMatrices.matrixMap A)
      (ZeroObservationMatrices.matrixMap B) (fun i => ZeroObservationMatrices.matrixMap (C i))
      (fun i => ZeroObservationMatrices.matrixMap (D i)) := by
  exact raw_exact_of_exactNull (EuclideanSpace.basisFun (Fin n) ℝ) (EuclideanSpace.basisFun (Fin r) ℝ)
    hW hWm hInd ⟨0,hm⟩ T hT (ZeroObservationMatrices.matrixMap A) (ZeroObservationMatrices.matrixMap B)
      (fun i => ZeroObservationMatrices.matrixMap (C i)) (fun i => ZeroObservationMatrices.matrixMap (D i))
      ((SurjectiveMatrices.stack_full_rank_iff D).mp hD)

end LinearStochastic.MatrixExactTerminal
