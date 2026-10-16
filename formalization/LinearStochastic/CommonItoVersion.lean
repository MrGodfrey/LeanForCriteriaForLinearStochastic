import LinearStochastic.CommonItoProcessGeneral

/-! Actual constructed Itô operators are invariant under indistinguishable
changes of the driving Brownian motion, with the original common filtration. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonItoVersion
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open CommonItoL2 CommonItoCLM CommonItoProcessGeneral
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {B C : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent B 𝓕 μ]
  [CommonItoIsometry.ForwardIndependent C 𝓕 μ]
  (hB : IsPreBrownianReal B μ) (hC : IsPreBrownianReal C μ)
  (hBm : ∀ t, Measurable (B t)) (hCm : ∀ t, Measurable (C t))
  (he : ∀ᵐ ω ∂μ, ∀ t, B t ω = C t ω)

include he

omit [IsProbabilityMeasure μ] [CommonItoIsometry.ForwardIndependent B 𝓕 μ]
  [CommonItoIsometry.ForwardIndependent C 𝓕 μ] in
/-- Literal finite increment sums agree on the common full-measure event. -/
theorem itoSimple_congr (V : SimpleProcess ℝ 𝓕) :
    itoSimple hBm V =ᵐ[μ] itoSimple hCm V := by
  filter_upwards [he] with ω hω
  simp only [itoSimple_apply,Finsupp.sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [hω p.2,hω p.1]

/-- Actual terminal continuous-linear Itô extensions are equal; the proof is
finite increment equality followed by density, not an asserted compatibility. -/
theorem integral_congr (T : ℝ≥0)
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm)) :
    itoIntegralCLM_T (𝓕:=𝓕) hB T hBm f = itoIntegralCLM_T (𝓕:=𝓕) hC T hCm f := by
  refine (simpleAssembly_T_denseRange (𝓕:=𝓕) (μ:=μ) T hBm).induction_on f
    (isClosed_eq (itoIntegralCLM_T (𝓕:=𝓕) hB T hBm).continuous
      (itoIntegralCLM_T (𝓕:=𝓕) hC T hCm).continuous) ?_
  intro V
  have hs : simpleAssembly_T (𝓕:=𝓕) (μ:=μ) T hBm V =
      simpleAssembly_T (𝓕:=𝓕) (μ:=μ) T hCm V := rfl
  rw [itoIntegralCLM_T_simpleAssembly_T]
  rw [hs,itoIntegralCLM_T_simpleAssembly_T]
  apply Lp.ext
  exact (memLp_itoSimple hB hBm V.val).coeFn_toLp.trans
    ((itoSimple_congr hBm hCm he V.val).trans (memLp_itoSimple hC hCm V.val).coeFn_toLp.symm)

/-- Every actual process-time operator is unchanged under this version repair. -/
theorem process_congr (T t : ℝ≥0)
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm)) :
    itoProcessCLM (𝓕:=𝓕) hB T t hBm f = itoProcessCLM (𝓕:=𝓕) hC T t hCm f := by
  rw [itoProcessCLM_eq_condExpL2,itoProcessCLM_eq_condExpL2,integral_congr hB hC hBm hCm he]

end LinearStochastic.CommonItoVersion
