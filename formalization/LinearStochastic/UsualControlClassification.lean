module

public import LinearStochastic.ActualControlProperties
public import LinearStochastic.UsualGlobalControllability

@[expose] public section

/-! Actual all-horizon approximate and approximate-null controllability are
exactly the vanishing of the genuine algebraic obstruction. This version uses
everywhere-continuous Brownian paths; version transport is stated separately. -/
noncomputable section
namespace LinearStochastic.UsualControlClassification
open MeasureTheory ProbabilityTheory
open scoped NNReal
open CommonItoMultichannel ActualControlProperties
open JointCylinderGeneration
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)
  (hWc : ∀ i ω, Continuous fun t => W i t ω)

include c in
/-- True AC and ANC are each equivalent to the actual terminal flag being
zero, for every prescribed positive horizon and all original coefficients. -/
theorem classification (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
      fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i
    (Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b hW hWm T A B C D ↔
      (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥) ∧
    (ApproximateNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b hW hWm T A B C D ↔
      (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i
  have hann := flag_zero_of_approximateNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
    b hW hWm T A B C D hWc i₀ (JointUsualIndependence.pairForward W hW hWm hInd hWc)
      (fun _ _ hij => hInd.indepFun hij)
  have hac : (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥ →
      Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b hW hWm T A B C D := by
    intro hf
    exact approximate_of_dense b hW hWm T A B C D c hWc i₀
      (UsualGlobalControllability.reachable_dense b c W hW hWm hInd hWc i₀ T hT A B C D hf)
  exact ⟨⟨fun h => hann (approximate_implies_approximateNull b hW hWm T A B C D h),hac⟩,
    ⟨hann,fun hf => approximate_implies_approximateNull b hW hWm T A B C D (hac hf)⟩⟩

end LinearStochastic.UsualControlClassification
