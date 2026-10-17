module

public import LinearStochastic.CommonItoMultichannel

@[expose] public section

noncomputable section
namespace LinearStochastic.CommonDirectionIntegral
open MeasureTheory ProbabilityTheory CommonItoCLM CommonItoL2
open scoped NNReal BigOperators Topology
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ι → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  [CommonItoIsometry.ForwardIndependent B 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hB : IsPreBrownianReal B μ) (hBm : ∀ t, Measurable (B t))
  (c : ι → ℝ) (hlinear : ∀ t ω, B t ω = ∑ i, c i * W i t ω)

include hlinear in
theorem simple_direction (V : SimpleProcess ℝ 𝓕) (ω : Ω) :
    itoSimple hBm V ω = ∑ i, c i * itoSimple (hWm i) V ω := by
  classical
  change (∑ p ∈ V.value.support, V.value p ω * (B p.2 ω - B p.1 ω)) =
    ∑ i, c i * (∑ p ∈ V.value.support, V.value p ω * (W i p.2 ω - W i p.1 ω))
  simp_rw [hlinear,←Finset.sum_sub_distrib,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  ring

include hlinear in
theorem simple_direction_Lp (V : SimpleProcess ℝ 𝓕) :
    itoSimpleLp hB hBm V = ∑ i, c i • itoSimpleLp (hW i) (hWm i) V := by
  apply Lp.ext
  have hi : ∀ᵐ ω ∂μ, ∀ i,
      (c i • itoSimpleLp (hW i) (hWm i) V) ω = c i * itoSimple (hWm i) V ω := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [Lp.coeFn_smul (c i) (itoSimpleLp (hW i) (hWm i) V),
      (memLp_itoSimple (hW i) (hWm i) V).coeFn_toLp] with ω h1 h2
    exact h1.trans (congrArg (fun z => c i * z) h2)
  filter_upwards [(memLp_itoSimple hB hBm V).coeFn_toLp,hi,
    Lp.coeFn_finsetSum Finset.univ (fun i => c i • itoSimpleLp (hW i) (hWm i) V)]
    with ω hBω hiω hsω
  change itoSimpleLp hB hBm V ω = itoSimple hBm V ω at hBω
  rw [hBω,hsω]
  simp only [Finset.sum_apply,hiω]
  exact simple_direction hWm hBm c hlinear V ω

include hlinear in
/-- Actual linearity in the Brownian driver, for the full predictable L²
integral on a specified common filtration. -/
theorem integral_direction (T : ℝ≥0)
    (f : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBm)) :
    itoIntegralCLM_T (𝓕 := 𝓕) hB T hBm f =
      ∑ i, c i • itoIntegralCLM_T (𝓕 := 𝓕) (hW i) T (hWm i) f := by
  refine (simpleAssembly_T_denseRange (𝓕 := 𝓕) (μ := μ) T hBm).induction_on f
    (isClosed_eq (itoIntegralCLM_T (𝓕 := 𝓕) hB T hBm).continuous
      (continuous_finsetSum _ (fun i _ =>
        (itoIntegralCLM_T (𝓕 := 𝓕) (hW i) T (hWm i)).continuous.const_smul (c i)))) ?_
  intro V
  rw [itoIntegralCLM_T_simpleAssembly_T]
  have hi (i : ι) :
      itoIntegralCLM_T (𝓕 := 𝓕) (hW i) T (hWm i) (simpleAssembly_T T hBm V) =
        itoSimpleLp (hW i) (hWm i) V.1 :=
    itoIntegralCLM_T_simpleAssembly_T (𝓕 := 𝓕) (hW i) T (hWm i) V
  simp_rw [hi]
  exact simple_direction_Lp hW hWm hB hBm c hlinear V.1

end LinearStochastic.CommonDirectionIntegral
