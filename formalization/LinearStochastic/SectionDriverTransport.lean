module

public import LinearStochastic.SectionLinearDuality
public import LinearStochastic.CommonItoVersion

@[expose] public section

/-! Actual vector integral solutions are invariant under indistinguishable
versions of the Brownian drivers, with the same filtration and original L²
classes. Only proved Itô operator equality is used. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.SectionDriverTransport
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct LinearDuality SectionLinearDuality

variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W V : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (V i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hV : ∀ i, IsPreBrownianReal (V i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hVm : ∀ i t, Measurable (V i t))
  (he : ∀ i, ∀ᵐ ω ∂μ, ∀ t, W i t ω = V i t ω)

include he in
omit [CompleteSpace E] in
/-- Every fixed-time vector Itô integral is unchanged almost surely. -/
theorem vectorProcess_ae (T t : ℝ≥0) (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    vectorProcess b hW hWm T φ t =ᵐ[μ] vectorProcess b hV hVm T φ t := by
  have hall : ∀ᵐ ω ∂μ, ∀ a i,
      CommonItoMartingaleVersion.integralProcess (hW i) T (hWm i) (coordinate b a (φ i)) t ω =
      CommonItoMartingaleVersion.integralProcess (hV i) T (hVm i) (coordinate b a (φ i)) t ω := by
    simp only [ae_all_iff]
    intro a i
    have hi := CommonItoVersion.process_congr (hW i) (hV i) (hWm i) (hVm i) (he i) T t (coordinate b a (φ i))
    exact (CommonItoMartingaleVersion.integralProcess_ae_eq (hW i) T t (hWm i) _).trans
      ((Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℝ 2 μ => (f : Ω → ℝ)) hi)).trans
        (CommonItoMartingaleVersion.integralProcess_ae_eq (hV i) T t (hVm i) _).symm)
  filter_upwards [hall] with ω hω
  simp only [vectorProcess,ItoExpectedProduct.sumProcess,hω]

include he in
omit [CompleteSpace E] in
/-- The genuine drift-and-Itô integral state is invariant at every time. -/
theorem integralState_ae (T : ℝ≥0) (s : ℝ) (ξ : Ω → E)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    integralState b hW hWm T ξ f φ s =ᵐ[μ] integralState b hV hVm T ξ f φ s := by
  filter_upwards [vectorProcess_ae b hW hV hWm hVm he T s.toNNReal φ] with ω hω
  simp only [integralState,hω]

include he in
omit [CompleteSpace E] in
/-- Both true time sections and the independently prescribed endpoint
transport to the indistinguishable Brownian version. -/
theorem solution (T : ℝ≥0) (ξ XT : Ω → E)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT) :
    SectionIntegralSolution b hV hVm T ξ f φ X XT := by
  constructor
  · filter_upwards [hX.sections] with s hs
    exact Filter.EventuallyEq.trans hs (integralState_ae b hW hV hWm hVm he T s ξ f φ)
  · exact hX.terminal.trans (integralState_ae b hW hV hWm hVm he T T ξ f φ)

end LinearStochastic.SectionDriverTransport
