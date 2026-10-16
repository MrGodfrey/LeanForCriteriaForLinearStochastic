import LinearStochastic.BSDEGlobalExistence
import LinearStochastic.JointUsualRepresentation

/-! Genuine arbitrary-horizon adjoint backward existence on the actual usual
augmentation of the Brownian natural filtration, on the original sample space. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.UsualGlobalBSDE
open MeasureTheory ProbabilityTheory
open scoped NNReal
variable {Ω ι κ : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι] [Fintype κ]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [μ.IsComplete]
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t))
  (hInd : iIndepFun (fun i ω t ↦ W i t ω) μ)
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

/-- No martingale-representation or small-time premise remains. The solution
contains actual continuous S² paths, predictable H² diffusion, literal adjoint
coefficients and the separate prescribed terminal boundary. -/
theorem exists_global (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ)
    (hη : ∀ b, AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T] (η b) μ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointCylinderGeneration.natural W hWm) μ :=
      fun i ↦ JointNaturalForward.coordinateForward W hW hWm hInd i
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      fun i ↦ JointUsualIndependence.coordinateForward W hW hWm hInd hWc i
    Nonempty (BSDEPathData.Solution (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      hW hWm T A C η) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointCylinderGeneration.natural W hWm) μ :=
    fun i ↦ JointNaturalForward.coordinateForward W hW hWm hInd i
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    fun i ↦ JointUsualIndependence.coordinateForward W hW hWm hInd hWc i
  exact BSDEGlobalExistence.exists_global hW hWm hWc
    (JointUsualIndependence.pairForward W hW hWm hInd hWc)
    (fun _ _ hij ↦ hInd.indepFun hij) i₀ T hT A C η hη
    (fun t ↦ JointUsualRepresentation.represented W hW hWm hInd hWc t)

end LinearStochastic.UsualGlobalBSDE
