module

public import LinearStochastic.CommonShiftH2
public import LinearStochastic.CommonItoLocality
public import LinearStochastic.CommonItoProcessGeneral

@[expose] public section

/-! Genuine finite stochastic increment sums under deterministic restart. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonShiftSimple
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonItoL2 CommonItoCLM CommonItoLocality CommonItoProcess
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent W 𝓕 μ]
  (hWm : ∀ t, Measurable (W t))

include hWm in
theorem shiftedMeas (a : ℝ≥0) : ∀ t, Measurable (CommonTimeShift.driver W a t) :=
  fun t ↦ (hWm (a+t)).sub (hWm a)

instance shiftedForward (a : ℝ≥0) :
    CommonItoIsometry.ForwardIndependent (CommonTimeShift.driver W a)
      (CommonTimeShift.filtration 𝓕 a) μ := CommonTimeShift.forwardIndependent a

/-- Subtract the restart time from every actual interval endpoint. Degenerate
intervals automatically contribute zero, including intervals entirely in the past. -/
def simpleShift (a δ : ℝ≥0) (V : TBoundedSP (𝓕:=𝓕) (a+δ) hWm) :
    TBoundedSP (𝓕:=CommonTimeShift.filtration 𝓕 a) δ (shiftedMeas hWm a) :=
  ∑ p ∈ V.val.value.support.attach,
    stepSP (shiftedMeas hWm a)
      (tsub_le_tsub_right (V.val.le_of_mem_support_value p.val p.property) a)
      (by simpa only [add_tsub_cancel_left] using tsub_le_tsub_right (V.property p.val p.property) a)
      ((V.val.measurable_value p.val).mono (𝓕.mono le_add_tsub) le_rfl)
      (M:=V.val.valueBound)
      (fun ω ↦ by rw [←Real.norm_eq_abs]; exact V.val.value_le_valueBound p.val ω)

/-- The shifted interval has exactly the original indicator after translation,
away from the time-zero null boundary. -/
theorem interval_translate (a s u t : ℝ≥0) (ht : 0 < t) :
    t ∈ Ioc (s-a) (u-a) ↔ a+t ∈ Ioc s u := by
  simp only [mem_Ioc]
  constructor
  · intro h
    constructor
    · by_cases has : a ≤ s
      · exact (tsub_lt_iff_left has).mp h.1
      · exact lt_of_le_of_lt (le_of_not_ge has) (lt_add_of_pos_right a ht)
    · have hau : a ≤ u := by
        by_contra hn
        have hu : u-a = 0 := tsub_eq_zero_of_le (le_of_not_ge hn)
        rw [hu] at h
        exact (not_le_of_gt ht) h.2
      calc a+t ≤ a+(u-a) := add_le_add le_rfl h.2
           _ = u := add_tsub_cancel_of_le hau
  · intro h
    constructor
    · by_cases has : a ≤ s
      · exact (tsub_lt_iff_left has).mpr h.1
      · rw [tsub_eq_zero_of_le (le_of_not_ge has)]
        exact ht
    · have hau : a ≤ u := (le_add_right le_rfl).trans h.2
      have hh : a+t ≤ a+(u-a) := by rw [add_tsub_cancel_of_le hau]; exact h.2
      exact (add_le_add_iff_left a).mp hh

/-- The finite shifted simple process is the actual translated original process. -/
theorem simpleShift_coe (a δ : ℝ≥0) (V : TBoundedSP (𝓕:=𝓕) (a+δ) hWm)
    {t : ℝ≥0} (ht : 0 < t) (ω : Ω) :
    (simpleShift hWm a δ V).val t ω = V.val (a+t) ω := by
  have hbot : a+t ∉ ({(⊥:ℝ≥0)} : Set ℝ≥0) := by
    simp only [mem_singleton_iff,NNReal.bot_eq_zero]
    exact ne_of_gt (lt_of_le_of_lt (show 0 ≤ a from zero_le) (lt_add_of_pos_right a ht))
  have hV : V.val (a+t) ω = ∑ p ∈ V.val.value.support,
      (Ioc p.1 p.2).indicator (fun _ ↦ V.val.value p ω) (a+t) := by
    rw [SimpleProcess.apply_eq,Set.indicator_of_notMem hbot,zero_add,Finsupp.sum]
  rw [simpleShift,AddSubmonoidClass.coe_finsetSum,coe_simpleProcess_sum,hV,
    ←Finset.sum_attach V.val.value.support (fun p ↦ (Ioc p.1 p.2).indicator (fun _ ↦ V.val.value p ω) (a+t))]
  apply Finset.sum_congr rfl
  intro p _
  rw [coe_stepSP]
  have he := interval_translate a p.val.1 p.val.2 t ht
  by_cases hi : a+t ∈ Ioc p.val.1 p.val.2
  · rw [Set.indicator_of_mem hi,Set.indicator_of_mem (he.mpr hi)]
  · rw [Set.indicator_of_notMem hi,Set.indicator_of_notMem (fun h ↦ hi (he.mp h))]

omit mΩ in
/-- The translated Brownian increment equals original full increment minus its
past part; the identity is proved for the actual endpoint order. -/
theorem increment_split (a s u : ℝ≥0) (hsu : s ≤ u) (ω : Ω) :
    CommonTimeShift.driver W a (u-a) ω - CommonTimeShift.driver W a (s-a) ω =
      (W u ω-W s ω) - (W (min u a) ω-W (min s a) ω) := by
  simp only [CommonTimeShift.driver,add_tsub_eq_max]
  by_cases hau : u ≤ a
  · rw [max_eq_left hau,max_eq_left (hsu.trans hau),min_eq_left hau,min_eq_left (hsu.trans hau)]
    ring
  · by_cases has : s ≤ a
    · rw [max_eq_right (le_of_not_ge hau),max_eq_left has,min_eq_right (le_of_not_ge hau),min_eq_left has]
      ring
    · rw [max_eq_right (le_of_not_ge hau),max_eq_right (le_of_not_ge has),min_eq_right (le_of_not_ge hau),min_eq_right (le_of_not_ge has)]
      ring

/-- Actual finite stochastic sums satisfy the restart difference formula. -/
theorem itoSimple_shift (a δ : ℝ≥0) (V : TBoundedSP (𝓕:=𝓕) (a+δ) hWm) (ω : Ω) :
    itoSimple (shiftedMeas hWm a) (simpleShift hWm a δ V).val ω =
      itoSimple hWm V.val ω - itoSimpleProcess hWm V.val a ω := by
  rw [simpleShift,AddSubmonoidClass.coe_finsetSum,itoSimple_sum]
  simp only [Finset.sum_apply]
  rw [itoSimple_apply,itoSimpleProcess_apply,Finsupp.sum,Finsupp.sum,←Finset.sum_sub_distrib,
    ←Finset.sum_attach V.val.value.support
      (fun p ↦ V.val.value p ω*(W p.2 ω-W p.1 ω)-V.val.value p ω*(W (min p.2 a) ω-W (min p.1 a) ω))]
  apply Finset.sum_congr rfl
  intro p _
  rw [itoSimple_stepSP,increment_split a p.val.1 p.val.2 (V.val.le_of_mem_support_value p.val p.property)]
  ring
end LinearStochastic.CommonShiftSimple
