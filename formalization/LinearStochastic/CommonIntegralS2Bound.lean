module

public import LinearStochastic.PathSupNorm

@[expose] public section

/-! Quantitative full-path bounds for the actual Lebesgue drift and Itô
representatives, not merely their values at a fixed terminal time. -/
noncomputable section
namespace LinearStochastic.CommonIntegralS2Bound
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open CommonItoCLM CommonVectorPicard CommonDriftS2 ContinuousDoobL2
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- Actual predictable integrand energy equals its ordinary product integral. -/
theorem energy (T : ℝ≥0) (g : H2 𝓕 μ T) :
    (∫ ω, ∫ s, g (s,ω)^2 ∂timeMeasure_T T ∂μ)=‖g‖^2 := by
  rw [←integral_prod_symm _ (integrand_product_memLp T g).integrable_sq,
    CommonItoL2.lp_two_norm_sq]
  exact integral_trim 𝓕.predictable_le_prod ((Lp.stronglyMeasurable g).pow 2)

/-- The true uncountable-time drift supremum obeys the sqrt(T) bound. -/
theorem rawDrift_norm (T : ℝ≥0) (g : H2 𝓕 μ T) :
    PathSupNorm.norm (μ:=μ) (rawDrift T g) T ≤ Real.sqrt (T:ℝ)*‖g‖ := by
  have hL := rawDrift_S2 T g
  have hi := (integrand_product_memLp T g).integrable_sq.integral_prod_right
  have he := integral_mono_ae (CommonDriftS2.integrable_pathSup_sq T g)
    (hi.const_mul (T:ℝ)) (pathSup_sq_bound T g)
  rw [integral_const_mul] at he
  change (∫ ω, pathSup (rawDrift T g) T ω^2 ∂μ) ≤ (T:ℝ)*(∫ ω, ∫ s, g (s,ω)^2 ∂timeMeasure_T T ∂μ) at he
  rw [energy T g,←PathSupNorm.sq_eq_integral T _ hL] at he
  have hn := PathSupNorm.nonneg (μ:=μ) (rawDrift T g) T
  have hr := Real.sqrt_nonneg (T:ℝ)
  have hs := Real.sq_sqrt T.coe_nonneg
  have hg := norm_nonneg g
  apply (sq_le_sq₀ hn (mul_nonneg hr hg)).mp
  rw [mul_pow,hs]
  exact he

variable {ι : Type*} [Fintype ι] {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t=>W i t ω)

omit [Fintype ι] in
/-- The specific continuous drift modification used in every Picard solution
has the same quantitative full-path bound. -/
theorem drift_norm (i : ι) (T : ℝ≥0) (g : H2 𝓕 μ T) :
    PathSupNorm.norm (μ:=μ) (CommonDriftPredictable.driftContinuousMod T (hWm i) g) T ≤
      Real.sqrt (T:ℝ)*‖g‖ := by
  have he : ∀ᵐ ω ∂μ, ∀ t, t≤T → CommonDriftPredictable.driftContinuousMod T (hWm i) g t ω = rawDrift T g t ω := by
    filter_upwards [driftContinuousMod_indistinguishable T (hWm i) g] with ω hω
    intro t ht
    simpa only [rawDrift,min_eq_left ht] using hω t ht
  rw [PathSupNorm.congr T he]
  exact rawDrift_norm T g

include hW hWc in
omit [Fintype ι] in
/-- Actual Doob L² yields the factor 2 for the very same Itô modification
used in the controlled path, via proved closed-interval indistinguishability. -/
theorem ito_norm [𝓕.IsComplete μ] (i : ι) (T : ℝ≥0) (g : H2 𝓕 μ T) :
    PathSupNorm.norm (μ:=μ) (CommonItoContinuous.itoContinuousMod T (hWm i) g) T ≤ 2*‖g‖ := by
  obtain ⟨Y,he,hc,hm,hy2,hbound,hint⟩ :=
    CommonFiltrationCompletion.exists_s2_on_complete_filtration (hW i) T (hWm i) (hWc i) g
  have hxc := CommonItoContinuous.itoContinuousMod_continuousOn (hW i) T (hWm i) (hWc i) g
  have hset : Icc (0:ℝ≥0) T=Iic T := by ext t; simp
  rw [hset] at hxc
  have heq := indistinguishable_on_Iic T _ Y hxc (ae_of_all _ (fun ω=>(hc ω).continuousOn))
    (fun t ht => (CommonItoContinuous.itoContinuousMod_modification (hW i) T (hWm i) (hWc i) g ht).trans (he t ht).symm)
  rw [PathSupNorm.congr T heq]
  have hb := ENNReal.toReal_mono (by finiteness : (2*‖g‖ₑ : ℝ≥0∞)≠⊤) hbound
  simpa only [PathSupNorm.norm,ENNReal.toReal_mul,ENNReal.toReal_ofNat,enorm,ENNReal.coe_toReal,
    coe_nnnorm] using hb

end LinearStochastic.CommonIntegralS2Bound
