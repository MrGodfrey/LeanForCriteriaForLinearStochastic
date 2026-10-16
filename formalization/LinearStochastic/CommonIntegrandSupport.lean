import LinearStochastic.CommonFiltrationTransport

noncomputable section
namespace LinearStochastic.CommonIntegrandSupport
open MeasureTheory
open scoped NNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {μ : Measure Ω}
  {𝓕 𝓖 : Filtration ℝ≥0 mΩ}

/-- A measurable event has the same almost-sure truth in the ambient measure
and its genuine trim. -/
theorem ae_trim_of_measurable {α : Type*} {m : MeasurableSpace α}
    [m₀ : MeasurableSpace α] (ν : Measure α) (hm : m ≤ m₀)
    {P : α → Prop} (hP : MeasurableSet[m] {x | P x}) (h : ∀ᵐ x ∂ν, P x) :
    ∀ᵐ x ∂ν.trim hm, P x := by
  rw [ae_iff]
  change (ν.trim hm) ({x | P x}ᶜ) = 0
  rw [trim_measurableSet_eq hm hP.compl]
  exact h

/-- Filtration inclusion preserves the actual integrand's vanishing before a
fixed time, with the ae statement in the larger predictable trim. -/
theorem inclusion_vanishes_before (h : 𝓕 ≤ 𝓖) (T a : ℝ≥0)
    (f : Lp ℝ 2 (((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod))
    (hf : ∀ᵐ p ∂(((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod),
      p.1 ≤ a → f p = 0) :
    ∀ᵐ p ∂(((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓖.predictable_le_prod),
      p.1 ≤ a → CommonFiltrationTransport.integrandInclusion h T f p = 0 := by
  have hm : MeasurableSet[𝓖.predictable] {p : ℝ≥0 × Ω | a < p.1} := by
    simpa only [Set.prod_univ,Set.preimage,Set.mem_Ioi] using
      measurableSet_predictable_Ioi_prod (𝓕 := 𝓖) (i := a) (MeasurableSet.univ : MeasurableSet[𝓖 a] (Set.univ : Set Ω))
  apply ae_trim_of_measurable _ 𝓖.predictable_le_prod
  · simp only [imp_iff_not_or,not_le]
    exact hm.union (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable measurable_const)
  · filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod hf,
      TrimInclusion.inclusion_ambient_ae ((CommonItoCLM.timeMeasure_T T).prod μ)
        𝓕.predictable_le_prod 𝓖.predictable_le_prod (TrimInclusion.predictable_mono h) f]
      with p hp he ha
    exact he.trans (hp ha)

/-- Filtration inclusion preserves the actual integrand's vanishing after a
fixed time, with the ae statement in the larger predictable trim. -/
theorem inclusion_vanishes_after (h : 𝓕 ≤ 𝓖) (T a : ℝ≥0)
    (f : Lp ℝ 2 (((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod))
    (hf : ∀ᵐ p ∂(((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod),
      a < p.1 → f p = 0) :
    ∀ᵐ p ∂(((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓖.predictable_le_prod),
      a < p.1 → CommonFiltrationTransport.integrandInclusion h T f p = 0 := by
  have hm : MeasurableSet[𝓖.predictable] {p : ℝ≥0 × Ω | p.1 ≤ a} := by
    simpa only [Set.prod_univ,Set.preimage,Set.mem_Ioi,Set.compl_ofPred,not_lt] using
      (measurableSet_predictable_Ioi_prod (𝓕 := 𝓖) (i := a) (MeasurableSet.univ : MeasurableSet[𝓖 a] (Set.univ : Set Ω))).compl
  apply ae_trim_of_measurable _ 𝓖.predictable_le_prod
  · simp only [imp_iff_not_or,not_lt]
    exact hm.union (measurableSet_eq_fun (Lp.stronglyMeasurable _).measurable measurable_const)
  · filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod hf,
      TrimInclusion.inclusion_ambient_ae ((CommonItoCLM.timeMeasure_T T).prod μ)
        𝓕.predictable_le_prod 𝓖.predictable_le_prod (TrimInclusion.predictable_mono h) f]
      with p hp he ha
    exact he.trans (hp ha)

end LinearStochastic.CommonIntegrandSupport
