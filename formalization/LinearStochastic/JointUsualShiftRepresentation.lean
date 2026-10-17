module

public import LinearStochastic.JointUsualRepresentation
public import LinearStochastic.CommonShiftRepresentation

@[expose] public section

noncomputable section
namespace LinearStochastic.JointUsualShiftRepresentation
open MeasureTheory ProbabilityTheory CommonTimeShift
open scoped NNReal
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t))
  (hInd : iIndepFun (fun i ω t => W i t ω) μ)
  (hWc : ∀ i ω, Continuous fun t => W i t ω)

/-- Actual martingale representation on every deterministic subinterval of
the original usual Brownian filtration, with the full original past retained.
Neither a shifted-natural-filtration replacement nor an MR oracle is used. -/
theorem represented (a δ : ℝ≥0) (F : Lp ℝ 2 μ)
    (hFm : AEStronglyMeasurable[filtration (JointUsualNatural.usual (μ := μ) W hWm) a δ] F μ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointCylinderGeneration.natural W hWm) μ :=
      fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ := μ) W hWm) μ :=
      fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i
    BSDEIntegralRange.Represented (𝓕 := filtration (JointUsualNatural.usual (μ := μ) W hWm) a)
      (fun i => preBrownian (hW i) a) (fun i => CommonShiftSimple.shiftedMeas (hWm i) a)
      (CommonShiftRepresentation.pair_shift (JointUsualIndependence.pairForward W hW hWm hInd hWc) a)
      (CommonShiftRepresentation.channels_shift (fun i j hij => hInd.indepFun hij) a) δ F := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointCylinderGeneration.natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointUsualNatural.usual (μ := μ) W hWm) μ :=
    fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i
  exact CommonShiftRepresentation.represented_shift hW hWm
    (JointUsualIndependence.pairForward W hW hWm hInd hWc)
    (fun _ _ hij => hInd.indepFun hij) a δ F
    (JointUsualRepresentation.represented W hW hWm hInd hWc (a+δ) F hFm)

end LinearStochastic.JointUsualShiftRepresentation
