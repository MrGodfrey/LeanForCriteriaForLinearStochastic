module

public import LinearStochastic.CommonShiftSimple

@[expose] public section

/-! Actual deterministic-restart compatibility of the constructed continuous
Itô operator, proved first on increment sums and then on their dense L² domain. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonShiftIntegral
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open CommonItoL2 CommonItoCLM CommonItoProcess CommonItoProcessGeneral CommonShiftSimple
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent W 𝓕 μ]
  (hW : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))

/-- The actual predictable restriction CLM sends a simple embedding to its
literal restarted finite-interval process. -/
theorem shift_simpleAssembly (a δ : ℝ≥0) (V : TBoundedSP (𝓕:=𝓕) (a+δ) hWm) :
    CommonShiftH2.shiftCLM a δ (a+δ) le_rfl (simpleAssembly_T (𝓕:=𝓕) (μ:=μ) (a+δ) hWm V) =
      simpleAssembly_T (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ (shiftedMeas hWm a)
        (simpleShift hWm a δ V) := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
    (CommonTimeShift.filtration 𝓕 a).predictable_le_prod (Lp.stronglyMeasurable _)
  have hf := ae_of_ae_trim 𝓕.predictable_le_prod
    (memLp_uncurry_trim_T (𝓕:=𝓕) (μ:=μ) (a+δ) hWm V.val).coeFn_toLp
  have hg := ae_of_ae_trim (CommonTimeShift.filtration 𝓕 a).predictable_le_prod
    (memLp_uncurry_trim_T (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ (shiftedMeas hWm a)
      (simpleShift hWm a δ V).val).coeFn_toLp
  change (simpleAssembly_T (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ (shiftedMeas hWm a)
    (simpleShift hWm a δ V) : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T δ).prod μ]
      Function.uncurry (simpleShift hWm a δ V).val at hg
  have ht : ∀ᵐ t ∂timeMeasure_T δ, 0 < t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.1
  filter_upwards [CommonShiftH2.shift_ae a δ (a+δ) le_rfl
      (simpleAssembly_T (𝓕:=𝓕) (μ:=μ) (a+δ) hWm V),
    CommonShiftH2.pull_ae a δ (a+δ) le_rfl hf,hg,
    Measure.quasiMeasurePreserving_fst.ae ht] with z hs hf hg ht
  exact hs.trans (hf.trans (by simpa only [Function.uncurry,trimMeasure_T,CommonShiftH2.Space] using
    (simpleShift_coe hWm a δ V ht z.2).symm.trans hg.symm))

/-- The restarted finite integral is the full original finite integral minus
its genuine stopped integral at the restart time. -/
theorem itoAssembly_shift (a δ : ℝ≥0) (V : TBoundedSP (𝓕:=𝓕) (a+δ) hWm) :
    itoAssembly_T (𝓕:=CommonTimeShift.filtration 𝓕 a) (CommonTimeShift.preBrownian hW a)
      δ (shiftedMeas hWm a) (simpleShift hWm a δ V) =
      itoAssembly_T (𝓕:=𝓕) hW (a+δ) hWm V - itoSimpleProcessLp hW hWm V.val a := by
  apply Lp.ext
  have h1 := (memLp_itoSimple (CommonTimeShift.preBrownian hW a) (shiftedMeas hWm a)
    (simpleShift hWm a δ V).val).coeFn_toLp
  have h2 := (memLp_itoSimple hW hWm V.val).coeFn_toLp
  have h3 := (memLp_itoSimpleProcess hW hWm V.val a).coeFn_toLp
  filter_upwards [h1,h2,h3,Lp.coeFn_sub (itoAssembly_T (𝓕:=𝓕) hW (a+δ) hWm V)
    (itoSimpleProcessLp hW hWm V.val a)] with ω h1 h2 h3 hs
  rw [hs,Pi.sub_apply]
  exact h1.trans ((itoSimple_shift hWm a δ V ω).trans (congrArg₂ (·-·) h2.symm h3.symm))

/-- The true continuous Itô operators satisfy deterministic restart for every
predictable L² integrand. No compatibility is an axiom or structure field. -/
theorem integral_shift (a δ : ℝ≥0)
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) (a+δ) hWm)) :
    itoIntegralCLM_T (𝓕:=CommonTimeShift.filtration 𝓕 a) (CommonTimeShift.preBrownian hW a)
      δ (shiftedMeas hWm a) (CommonShiftH2.shiftCLM a δ (a+δ) le_rfl f) =
      itoIntegralCLM_T (𝓕:=𝓕) hW (a+δ) hWm f - itoProcessCLM hW (a+δ) a hWm f := by
  refine (simpleAssembly_T_denseRange (𝓕:=𝓕) (μ:=μ) (a+δ) hWm).induction_on f
    (isClosed_eq ((itoIntegralCLM_T (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (CommonTimeShift.preBrownian hW a) δ (shiftedMeas hWm a)).continuous.comp
        (CommonShiftH2.shiftCLM (𝓕:=𝓕) (μ:=μ) a δ (a+δ) le_rfl).continuous)
      ((itoIntegralCLM_T (𝓕:=𝓕) hW (a+δ) hWm).continuous.sub
        (itoProcessCLM hW (a+δ) a hWm).continuous)) ?_
  intro V
  rw [shift_simpleAssembly hWm a δ V,itoIntegralCLM_T_simpleAssembly_T,
    itoIntegralCLM_T_simpleAssembly_T,itoProcessCLM_simpleAssembly_T]
  exact itoAssembly_shift hW hWm a δ V
end LinearStochastic.CommonShiftIntegral
