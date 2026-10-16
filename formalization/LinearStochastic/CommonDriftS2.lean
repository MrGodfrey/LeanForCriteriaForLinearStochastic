import LinearStochastic.CommonPicardRealization
import LinearStochastic.ContinuousDoobL2
import LinearStochastic.ProgressivePredictable
import LinearStochastic.CommonContinuousUniqueness

/-! Actual Lebesgue drift path estimates for arbitrary predictable H² inputs.
This uses pathwise Cauchy–Schwarz and Fubini; the drift is not treated as a
martingale. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonDriftS2
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open CommonItoL2 CommonItoCLM CommonVectorPicard ContinuousDoobL2
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

def rawDrift (T : ℝ≥0) (g : H2 𝓕 μ T) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in Ioc (0 : ℝ≥0) (min t T), g (s,ω) ∂timeMeasure

omit [IsProbabilityMeasure μ] in
theorem integrand_product_memLp (T : ℝ≥0) (g : H2 𝓕 μ T) :
    MemLp (g : ℝ≥0 × Ω → ℝ) 2 ((timeMeasure_T T).prod μ) :=
  memLp_of_memLp_trim 𝓕.predictable_le_prod (Lp.memLp g)

theorem integrand_slice_memLp (T : ℝ≥0) (g : H2 𝓕 μ T) :
    ∀ᵐ ω ∂μ, MemLp (fun s ↦ g (s,ω)) 2 (timeMeasure_T T) := by
  have hp := integrand_product_memLp T g
  filter_upwards [hp.1.prodMk_right, hp.integrable_sq.prod_left_ae] with ω hm hi
  exact (memLp_two_iff_integrable_sq hm).mpr hi

omit [IsProbabilityMeasure μ] in
theorem rawDrift_stronglyAdapted (T : ℝ≥0) (g : H2 𝓕 μ T) :
    StronglyAdapted 𝓕 (rawDrift T g) := by
  have hp : IsStronglyPredictable 𝓕 (fun t ω ↦ g (t,ω)) := Lp.stronglyMeasurable g
  have ha := ProgressivePredictable.primitive_stronglyAdapted hp.isStronglyProgressive
  intro t
  have he : rawDrift T g t = ProgressivePredictable.primitive (fun s ω ↦ g (s,ω)) (min t T) := by
    funext ω
    exact (RealTimeBridge.integral_real_extension (min t T) (fun s ↦ g (s,ω))).symm
  rw [he]
  exact (ha (min t T)).mono (𝓕.mono (min_le_left t T))

/-- The true Lebesgue primitive has continuous paths almost surely, after
clamping at the horizon. This is not an assumed regularity of the input. -/
theorem rawDrift_continuous (T : ℝ≥0) (g : H2 𝓕 μ T) :
    ∀ᵐ ω ∂μ, Continuous (fun t ↦ rawDrift T g t ω) := by
  filter_upwards [integrand_slice_memLp T g] with ω hω
  have hm := hω.comp_measurePreserving (RealTimeBridge.toNNReal_measurePreserving T)
  have hint : IntervalIntegrable (fun s : ℝ ↦ g (s.toNNReal,ω)) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg]
    exact hm.integrable one_le_two
  have hc := intervalIntegral.continuousOn_primitive_interval' hint (show (0:ℝ) ∈ uIcc (0:ℝ) (T:ℝ) from left_mem_uIcc)
  have hmap : MapsTo (fun t : ℝ≥0 ↦ (min t T : ℝ≥0).toReal) univ (uIcc (0:ℝ) T) := by
    intro t _
    rw [uIcc_of_le T.coe_nonneg]
    exact ⟨(min t T).coe_nonneg,by exact_mod_cast min_le_right t T⟩
  have he : (fun t ↦ rawDrift T g t ω) =
      fun t : ℝ≥0 ↦ ∫ s in (0:ℝ)..(min t T : ℝ≥0), g (s.toNNReal,ω) := by
    funext t
    rw [intervalIntegral.integral_of_le (min t T).coe_nonneg]
    exact (RealTimeBridge.integral_real_extension (min t T) (fun s ↦ g (s,ω))).symm
  rw [he]
  exact continuousOn_univ.mp
    (hc.comp (NNReal.continuous_coe.comp (continuous_id.min continuous_const)).continuousOn hmap)

omit [IsProbabilityMeasure μ] in
/-- Countable dense maxima prove measurability of the whole-interval supremum
when paths are only almost surely continuous. -/
theorem pathSup_aestronglyMeasurable_ae {E : Type*} [NormedAddCommGroup E] {X : ℝ≥0 → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hc : ∀ᵐ ω ∂μ, Continuous (fun t ↦ X t ω)) (T : ℝ≥0) :
    AEStronglyMeasurable (pathSup X T) μ := by
  letI : Nonempty (Set.Iic T) := ⟨⟨T, show T ≤ T from le_rfl⟩⟩
  let q := TopologicalSpace.denseSeq (Set.Iic T)
  let f : ℕ → Ω → ℝ := fun n ω ↦ (sampleSet T q n).sup' (sampleSet_nonempty T q n) (fun t ↦ ‖X t ω‖)
  apply aestronglyMeasurable_of_tendsto_ae (f:=f) atTop
  · intro n
    apply Measurable.aestronglyMeasurable
    convert (Finset.measurable_sup' (sampleSet_nonempty T q n)
      (fun t _ ↦ ((hX t).mono (𝓕.le t)).norm.measurable)) using 1
    funext ω
    exact (Finset.sup'_apply (sampleSet_nonempty T q n) (fun t ω ↦ ‖X t ω‖) ω).symm
  · filter_upwards [hc] with ω hω
    exact sampled_max_tendsto X T q (TopologicalSpace.denseRange_denseSeq _) ω hω

/-- The deterministic whole-path Cauchy–Schwarz bound, simultaneously for
all observation times, follows from actual slice L² integrability. -/
theorem rawDrift_sq_bound (T : ℝ≥0) (g : H2 𝓕 μ T) :
    ∀ᵐ ω ∂μ, ∀ t, rawDrift T g t ω ^ 2 ≤
      (T : ℝ) * ∫ s in Ioc (0 : ℝ≥0) T, g (s,ω)^2 ∂timeMeasure := by
  filter_upwards [integrand_slice_memLp T g] with ω hω
  intro t
  let a := min t T
  have hle : a ≤ T := min_le_right _ _
  haveI : IsFiniteMeasure (timeMeasure.restrict (Ioc (0 : ℝ≥0) a)) :=
    ⟨by rw [Measure.restrict_apply_univ,timeMeasure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hsmall : MemLp (fun s ↦ g (s,ω)) 2 (timeMeasure.restrict (Ioc (0 : ℝ≥0) a)) :=
    hω.mono_measure (Measure.restrict_mono (Ioc_subset_Ioc_right hle) le_rfl)
  calc
    _ ≤ (timeMeasure.restrict (Ioc (0 : ℝ≥0) a)).real univ *
        ∫ s in Ioc (0 : ℝ≥0) a, g (s,ω)^2 ∂timeMeasure :=
      MathFin.sq_integral_le_measureReal_mul hsmall
    _ ≤ (T : ℝ) * ∫ s in Ioc (0 : ℝ≥0) T, g (s,ω)^2 ∂timeMeasure := by
      rw [measureReal_def,Measure.restrict_apply_univ,timeMeasure_Ioc,
        NNReal.coe_zero,sub_zero,ENNReal.toReal_ofReal a.coe_nonneg]
      apply mul_le_mul (show (a : ℝ) ≤ T by exact_mod_cast hle) _
        (integral_nonneg fun s ↦ sq_nonneg _) T.coe_nonneg
      exact setIntegral_mono_set hω.integrable_sq (ae_of_all _ fun s ↦ sq_nonneg _)
        (Ioc_subset_Ioc_right hle).eventuallyLE

/-- The full uncountable-time squared supremum is bounded by the actual
integrand energy, with no martingale estimate for the drift. -/
theorem pathSup_sq_bound (T : ℝ≥0) (g : H2 𝓕 μ T) :
    ∀ᵐ ω ∂μ, pathSup (rawDrift T g) T ω ^ 2 ≤
      (T : ℝ) * ∫ s in Ioc (0 : ℝ≥0) T, g (s,ω)^2 ∂timeMeasure := by
  letI : Nonempty (Iic T) := ⟨⟨T,show T ≤ T from le_rfl⟩⟩
  filter_upwards [rawDrift_sq_bound T g] with ω hω
  let R := (T : ℝ) * ∫ s in Ioc (0 : ℝ≥0) T, g (s,ω)^2 ∂timeMeasure
  have hR : 0 ≤ R := mul_nonneg T.coe_nonneg (integral_nonneg fun s ↦ sq_nonneg _)
  have hs : pathSup (rawDrift T g) T ω ≤ Real.sqrt R := by
    apply ciSup_le
    intro t
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (hω t.val)
  have hn : 0 ≤ pathSup (rawDrift T g) T ω := Real.iSup_nonneg fun t ↦ norm_nonneg _
  have hp := mul_self_le_mul_self hn hs
  simpa only [← pow_two,Real.sq_sqrt hR] using hp

/-- Actual square integrability of the full drift path supremum. -/
theorem integrable_pathSup_sq (T : ℝ≥0) (g : H2 𝓕 μ T) :
    Integrable (fun ω ↦ pathSup (rawDrift T g) T ω ^ 2) μ := by
  have hm := pathSup_aestronglyMeasurable_ae (rawDrift_stronglyAdapted T g) (rawDrift_continuous T g) T
  have henergy := (integrand_product_memLp T g).integrable_sq.integral_prod_right
  apply (henergy.const_mul (T : ℝ)).mono' (hm.pow 2)
  filter_upwards [pathSup_sq_bound T g] with ω hω
  change |pathSup (rawDrift T g) T ω ^ 2| ≤ _
  rw [abs_of_nonneg (sq_nonneg _)]
  exact hω

theorem rawDrift_S2 (T : ℝ≥0) (g : H2 𝓕 μ T) :
    MemLp (pathSup (rawDrift T g) T) 2 μ :=
  (memLp_two_iff_integrable_sq
    (pathSup_aestronglyMeasurable_ae (rawDrift_stronglyAdapted T g) (rawDrift_continuous T g) T)).mpr
    (integrable_pathSup_sq T g)

omit [IsProbabilityMeasure μ] in
/-- Closed-interval indistinguishability follows from actual modifications and
continuous paths by applying the countable-dense-set theorem on the subtype. -/
theorem indistinguishable_on_Iic {E : Type*} [TopologicalSpace E] [T2Space E]
    (T : ℝ≥0) (X Y : ℝ≥0 → Ω → E)
    (hX : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Iic T))
    (hY : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ Y t ω) (Iic T))
    (h : ∀ t, t ≤ T → X t =ᵐ[μ] Y t) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ T → X t ω = Y t ω := by
  have hx : ∀ᵐ ω ∂μ, Continuous (fun t : Iic T ↦ X t.val ω) :=
    hX.mono fun ω hω ↦ continuousOn_iff_continuous_domRestrict.mp hω
  have hy : ∀ᵐ ω ∂μ, Continuous (fun t : Iic T ↦ Y t.val ω) :=
    hY.mono fun ω hω ↦ continuousOn_iff_continuous_domRestrict.mp hω
  have he := indistinguishable_of_modification hx hy (fun t : Iic T ↦ h t.val t.property)
  filter_upwards [he] with ω hω
  exact fun t ht ↦ hω ⟨t,ht⟩

omit [IsProbabilityMeasure μ] in
theorem pathSup_congr {E : Type*} [NormedAddCommGroup E]
    (T : ℝ≥0) {X Y : ℝ≥0 → Ω → E}
    (h : ∀ᵐ ω ∂μ, ∀ t, t ≤ T → X t ω = Y t ω) :
    pathSup X T =ᵐ[μ] pathSup Y T := by
  filter_upwards [h] with ω hω
  unfold pathSup
  congr 1
  funext t
  rw [hω t.val t.property]

/-- The actual drift modification agrees with its raw Lebesgue integral
simultaneously at every time on the closed horizon. -/
theorem driftContinuousMod_indistinguishable {B : ℝ≥0 → Ω → ℝ}
    [CommonItoIsometry.ForwardIndependent B 𝓕 μ]
    (T : ℝ≥0) (hBm : ∀ t, Measurable (B t)) (g : H2 𝓕 μ T) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ T → CommonDriftPredictable.driftContinuousMod T hBm g t ω =
      ∫ s in Ioc (0 : ℝ≥0) t, g (s,ω) ∂timeMeasure := by
  have hc := CommonDriftPathwise.driftContinuousMod_continuousOn T hBm g
  have hset : Icc (0 : ℝ≥0) T = Iic T := by ext t; simp
  rw [hset] at hc
  have he : ∀ᵐ ω ∂μ, ∀ t, t ≤ T → CommonDriftPredictable.driftContinuousMod T hBm g t ω = rawDrift T g t ω := by
    apply indistinguishable_on_Iic T _ (rawDrift T g) hc
      ((rawDrift_continuous T g).mono fun _ h ↦ h.continuousOn)
    intro t ht
    filter_upwards [CommonDriftModification.driftContinuousMod_eq_setIntegral T hBm g ht] with ω hω
    change _ = ∫ s in Ioc (0 : ℝ≥0) (min t T), g (s,ω) ∂timeMeasure
    simpa only [min_eq_left ht, trimMeasure_T, CommonItoMultichannel.spacetimeMeasure] using hω
  filter_upwards [he] with ω hω
  intro t ht
  simpa only [rawDrift,min_eq_left ht] using hω t ht

/-- The actual continuous-limit representative of the drift has full S²
integrability because it is indistinguishable from the raw Lebesgue primitive. -/
theorem driftContinuousMod_S2 {B : ℝ≥0 → Ω → ℝ}
    [CommonItoIsometry.ForwardIndependent B 𝓕 μ]
    (T : ℝ≥0) (hBm : ∀ t, Measurable (B t)) (g : H2 𝓕 μ T) :
    MemLp (pathSup (CommonDriftPredictable.driftContinuousMod T hBm g) T) 2 μ := by
  have he : ∀ᵐ ω ∂μ, ∀ t, t ≤ T → CommonDriftPredictable.driftContinuousMod T hBm g t ω = rawDrift T g t ω := by
    filter_upwards [driftContinuousMod_indistinguishable T hBm g] with ω hω
    intro t ht
    simpa only [rawDrift,min_eq_left ht] using hω t ht
  exact (memLp_congr_ae (pathSup_congr T he)).mpr (rawDrift_S2 T g)

end LinearStochastic.CommonDriftS2
