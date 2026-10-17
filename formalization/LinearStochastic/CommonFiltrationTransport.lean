module

public import LinearStochastic.TrimInclusion
public import LinearStochastic.CommonItoCLM

@[expose] public section

noncomputable section
namespace LinearStochastic.CommonFiltrationTransport
open MeasureTheory ProbabilityTheory CommonItoCLM
open scoped NNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 𝓖 : Filtration ℝ≥0 mΩ}

def integrandInclusion (h : 𝓕 ≤ 𝓖) (T : ℝ≥0) :
    Lp ℝ 2 (((timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod) →ₗᵢ[ℝ]
      Lp ℝ 2 (((timeMeasure_T T).prod μ).trim 𝓖.predictable_le_prod) :=
  TrimInclusion.inclusion _ 𝓕.predictable_le_prod 𝓖.predictable_le_prod
    (TrimInclusion.predictable_mono h)

def simpleLift (h : 𝓕 ≤ 𝓖) (V : SimpleProcess ℝ 𝓕) : SimpleProcess ℝ 𝓖 where
  valueBot := V.valueBot
  value := V.value
  le_of_mem_support_value := V.le_of_mem_support_value
  measurable_valueBot := V.measurable_valueBot.mono (h 0) le_rfl
  measurable_value' p _ := (V.measurable_value p).mono (h p.1) le_rfl
  bounded_valueBot := V.bounded_valueBot
  bounded_value := V.bounded_value

theorem simpleLift_coe (h : 𝓕 ≤ 𝓖) (V : SimpleProcess ℝ 𝓕) :
    (⇑(simpleLift h V)) = ⇑V := rfl

variable {B : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent B 𝓕 μ]
  [CommonItoIsometry.ForwardIndependent B 𝓖 μ]
  (hB : IsPreBrownianReal B μ) (hBm : ∀ t, Measurable (B t))

def boundedLift (h : 𝓕 ≤ 𝓖) (T : ℝ≥0)
    (V : TBoundedSP (𝓕 := 𝓕) T hBm) : TBoundedSP (𝓕 := 𝓖) T hBm :=
  ⟨simpleLift h V.1,V.2⟩

/-- Actual sample functions agree after embedding a simple integrand into the
larger predictable sigma algebra. -/
theorem inclusion_simple (h : 𝓕 ≤ 𝓖) (T : ℝ≥0)
    (V : TBoundedSP (𝓕 := 𝓕) T hBm) :
    integrandInclusion (μ := μ) h T (simpleAssembly_T (𝓕 := 𝓕) T hBm V) =
      simpleAssembly_T (𝓕 := 𝓖) T hBm (boundedLift hBm h T V) := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable 𝓖.predictable_le_prod
    (Lp.stronglyMeasurable _)
  have h1 := TrimInclusion.inclusion_ambient_ae ((timeMeasure_T T).prod μ)
    𝓕.predictable_le_prod 𝓖.predictable_le_prod (TrimInclusion.predictable_mono h)
    (simpleAssembly_T (𝓕 := 𝓕) (μ := μ) T hBm V)
  have h2 := ae_eq_of_ae_eq_trim
    (memLp_uncurry_trim_T (𝓕 := 𝓕) (μ := μ) T hBm V.1).coeFn_toLp
  have h3 := ae_eq_of_ae_eq_trim
    (memLp_uncurry_trim_T (𝓕 := 𝓖) (μ := μ) T hBm (boundedLift hBm h T V).1).coeFn_toLp
  exact h1.trans (h2.trans h3.symm)

/-- Finite stochastic increment sums are unchanged by the filtration lift. -/
theorem ito_simple_lift (h : 𝓕 ≤ 𝓖) (T : ℝ≥0)
    (V : TBoundedSP (𝓕 := 𝓕) T hBm) :
    itoAssembly_T (𝓕 := 𝓖) hB T hBm (boundedLift hBm h T V) =
      itoAssembly_T (𝓕 := 𝓕) hB T hBm V := by
  rfl

/-- The two actual continuous Itô extensions agree when the same integrand is
viewed in a larger admissible filtration. -/
theorem integral_inclusion (h : 𝓕 ≤ 𝓖) (T : ℝ≥0)
    (f : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBm)) :
    itoIntegralCLM_T (𝓕 := 𝓖) hB T hBm (integrandInclusion h T f) =
      itoIntegralCLM_T (𝓕 := 𝓕) hB T hBm f := by
  refine (simpleAssembly_T_denseRange (𝓕 := 𝓕) (μ := μ) T hBm).induction_on f
    (isClosed_eq ((itoIntegralCLM_T (𝓕 := 𝓖) hB T hBm).continuous.comp
      (integrandInclusion h T).continuous) (itoIntegralCLM_T (𝓕 := 𝓕) hB T hBm).continuous) ?_
  intro V
  rw [inclusion_simple hBm h T V,itoIntegralCLM_T_simpleAssembly_T,
    itoIntegralCLM_T_simpleAssembly_T]
  exact ito_simple_lift hB hBm h T V

end LinearStochastic.CommonFiltrationTransport
