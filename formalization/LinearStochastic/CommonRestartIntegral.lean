import LinearStochastic.CommonShiftIntegral
import LinearStochastic.CommonHorizonRestriction

/-! Restart compatibility for all times and arbitrary containing horizons. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonRestartIntegral
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open CommonItoL2 CommonItoCLM CommonItoProcessGeneral CommonShiftSimple CommonShiftH2
open CommonHorizonRestriction
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent W 𝓕 μ]
  (hW : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))

/-- Prefix restriction and actual translation agree as predictable L² classes. -/
theorem shift_restriction (a δ T : ℝ≥0) (h : a+δ ≤ T)
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hWm)) :
    shiftCLM a δ (a+δ) le_rfl (restriction hWm h f) = shiftCLM a δ T h f := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
    (CommonTimeShift.filtration 𝓕 a).predictable_le_prod (Lp.stronglyMeasurable _)
  have hr := ae_of_ae_trim 𝓕.predictable_le_prod (restriction_ae hWm h f)
  filter_upwards [shift_ae a δ (a+δ) le_rfl (restriction hWm h f),shift_ae a δ T h f,
    pull_ae a δ (a+δ) le_rfl hr] with z hl hr he
  exact hl.trans (he.trans hr.symm)

/-- General-horizon terminal restart identity for the actual Itô integrals. -/
theorem terminal_restart (a δ T : ℝ≥0) (h : a+δ ≤ T)
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hWm)) :
    itoIntegralCLM_T (𝓕:=CommonTimeShift.filtration 𝓕 a) (CommonTimeShift.preBrownian hW a)
      δ (shiftedMeas hWm a) (shiftCLM a δ T h f) =
      itoProcessCLM hW T (a+δ) hWm f - itoProcessCLM hW T a hWm f := by
  rw [←shift_restriction hWm a δ T h f,CommonShiftIntegral.integral_shift hW hWm,
    terminal_restriction hW hWm h,process_restriction hW hWm (show a ≤ a+δ from le_add_right le_rfl) h]

/-- Stopping a translated integrand shortens only its horizon, not its actual
values. Both sides represent precisely f(a+s,ω). -/
theorem restriction_shift (a δ T s : ℝ≥0) (h : a+δ ≤ T) (hs : s ≤ δ)
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hWm)) :
    restriction (𝓕:=CommonTimeShift.filtration 𝓕 a) (shiftedMeas hWm a) hs
      (shiftCLM a δ T h f) = shiftCLM a s T ((add_le_add le_rfl hs).trans h) f := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
    (CommonTimeShift.filtration 𝓕 a).predictable_le_prod (Lp.stronglyMeasurable _)
  have hr := ae_of_ae_trim (CommonTimeShift.filtration 𝓕 a).predictable_le_prod
    (restriction_ae (𝓕:=CommonTimeShift.filtration 𝓕 a) (shiftedMeas hWm a) hs (shiftCLM a δ T h f))
  have hm : (timeMeasure_T s).prod μ ≤ (timeMeasure_T δ).prod μ :=
    Measure.prod_mono (Measure.restrict_mono (by intro t ht; exact ⟨ht.1,ht.2.trans hs⟩) le_rfl) le_rfl
  filter_upwards [hr,(shift_ae a δ T h f).filter_mono (ae_mono hm),
    shift_ae a s T ((add_le_add le_rfl hs).trans h) f] with z hr hd hs
  exact hr.trans (hd.trans hs.symm)

/-- Every restarted process time is the corresponding original increment, as
an equality in actual sample L². The proof never interchanges arbitrary null sets. -/
theorem process_restart (a δ T s : ℝ≥0) (h : a+δ ≤ T) (hs : s ≤ δ)
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hWm)) :
    itoProcessCLM (𝓕:=CommonTimeShift.filtration 𝓕 a) (CommonTimeShift.preBrownian hW a)
      δ s (shiftedMeas hWm a) (shiftCLM a δ T h f) =
      itoProcessCLM hW T (a+s) hWm f - itoProcessCLM hW T a hWm f := by
  have ht := terminal_restriction (𝓕:=CommonTimeShift.filtration 𝓕 a)
    (CommonTimeShift.preBrownian hW a) (shiftedMeas hWm a) hs (shiftCLM a δ T h f)
  rw [restriction_shift hWm a δ T s h hs f] at ht
  exact ht.symm.trans (terminal_restart hW hWm a s T ((add_le_add le_rfl hs).trans h) f)
end LinearStochastic.CommonRestartIntegral
