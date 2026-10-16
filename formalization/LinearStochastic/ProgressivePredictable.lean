import LinearStochastic.RealTimeBridge
import BrownianMotion.StochasticIntegral.Predictable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-! Constructive progressive-to-predictable approximation via actual past
Lebesgue integrals. This file develops the required measurable/continuous
averages rather than postulating equivalence of the two control spaces. -/
noncomputable section
namespace LinearStochastic.ProgressivePredictable
open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped NNReal ENNReal
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {𝓕 : Filtration ℝ≥0 mΩ} {f : ℝ≥0 → Ω → E}

def primitive (f : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : E :=
  ∫ s in Ioc 0 (t : ℝ), f s.toNNReal ω

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Progressiveness makes the whole stopped past jointly measurable relative
to F_t; separate adaptedness would not suffice for this integral step. -/
theorem progressive_clamp_measurable (hf : IsStronglyProgressive 𝓕 f) (t : ℝ≥0) :
    StronglyMeasurable[(inferInstance : MeasurableSpace ℝ≥0).prod (𝓕 t)]
      (fun z : ℝ≥0 × Ω => f (min z.1 t) z.2) := by
  letI : MeasurableSpace Ω := 𝓕 t
  exact (hf t).comp_measurable
    (((measurable_fst.min measurable_const).subtype_mk (h := fun z => min_le_right z.1 t)).prodMk measurable_snd)

/-- The actual past Lebesgue primitive is strongly adapted, even before any
path-continuity repair or augmentation of the filtration. -/
theorem primitive_stronglyAdapted (hf : IsStronglyProgressive 𝓕 f) :
    StronglyAdapted 𝓕 (primitive f) := by
  intro t
  have he : primitive f t = fun ω =>
      ∫ s, f (min s t) ω ∂(CommonItoCLM.timeMeasure_T t) := by
    funext ω
    unfold primitive
    refine (RealTimeBridge.integral_real_extension t (fun s => f s ω)).trans ?_
    apply integral_congr_ae
    have hs : ∀ᵐ s ∂(CommonItoCLM.timeMeasure_T t), s ≤ t :=
      (ae_restrict_mem measurableSet_Ioc).mono (fun _ h => h.2)
    filter_upwards [hs] with s hs
    rw [min_eq_left hs]
  rw [he]
  have hm := progressive_clamp_measurable hf t
  letI : MeasurableSpace Ω := 𝓕 t
  exact hm.integral_prod_left'

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Clamping a progressive process at a deterministic horizon preserves the
full progressive property, since the clamped time never exceeds current time. -/
theorem progressive_clamp (hf : IsStronglyProgressive 𝓕 f) (T : ℝ≥0) :
    IsStronglyProgressive 𝓕 (fun t ω => f (min t T) ω) := by
  apply hf.comp
  · intro t
    letI : MeasurableSpace Ω := 𝓕 t
    exact ((measurable_subtype_coe.comp measurable_fst).min measurable_const).stronglyMeasurable
  · exact fun t _ => min_le_left t T

omit mΩ [CompleteSpace E] in
/-- Local path integrability gives actual path continuity of the past primitive. -/
theorem primitive_continuous
    (hi : ∀ ω, LocallyIntegrable (fun s : ℝ => f s.toNNReal ω) volume) (ω : Ω) :
    Continuous (fun t : ℝ≥0 => primitive f t ω) := by
  have hint (a b : ℝ) : IntervalIntegrable (fun s : ℝ => f s.toNNReal ω) volume a b :=
    intervalIntegrable_iff.mpr
      (((hi ω).integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)
  have hc := (intervalIntegral.continuous_primitive hint 0).comp NNReal.continuous_coe
  have he : (fun t : ℝ≥0 => primitive f t ω) =
      (fun b : ℝ => ∫ x in (0 : ℝ)..b, f x.toNNReal ω) ∘ NNReal.toReal := by
    funext t
    exact (intervalIntegral.integral_of_le (NNReal.coe_nonneg t)).symm
  rw [he]
  exact hc

/-- The averaging window always lies in the observed past. -/
def pastAverage (δ : ℝ≥0) (f : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : E :=
  (δ : ℝ)⁻¹ • (primitive f t ω - primitive f (t - δ) ω)

theorem pastAverage_stronglyAdapted (hf : IsStronglyProgressive 𝓕 f) (δ : ℝ≥0) :
    StronglyAdapted 𝓕 (pastAverage δ f) := by
  intro t
  have hnow := primitive_stronglyAdapted hf t
  have hpast := (primitive_stronglyAdapted hf (t - δ)).mono (𝓕.mono (tsub_le_self))
  exact (hnow.sub hpast).const_smul _

omit mΩ [CompleteSpace E] in
theorem pastAverage_continuous
    (hi : ∀ ω, LocallyIntegrable (fun s : ℝ => f s.toNNReal ω) volume)
    (δ : ℝ≥0) (ω : Ω) : Continuous (fun t => pastAverage δ f t ω) := by
  exact ((primitive_continuous hi ω).sub
    ((primitive_continuous hi ω).comp (continuous_id.sub continuous_const))).const_smul _

/-- Each genuine past average is predictable by continuity and strong adaptedness. -/
theorem pastAverage_predictable (hf : IsStronglyProgressive 𝓕 f)
    (hi : ∀ ω, LocallyIntegrable (fun s : ℝ => f s.toNNReal ω) volume) (δ : ℝ≥0) :
    IsStronglyPredictable 𝓕 (pastAverage δ f) :=
  (pastAverage_stronglyAdapted hf δ).isStronglyPredictable_of_leftContinuous
    (fun ω _t => (pastAverage_continuous hi δ ω).continuousAt.continuousWithinAt)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Clamping produces globally measurable paths from the exact progressive hypothesis. -/
theorem clamped_path_stronglyMeasurable (hf : IsStronglyProgressive 𝓕 f)
    (T : ℝ≥0) (ω : Ω) :
    StronglyMeasurable (fun s : ℝ => f (min s.toNNReal T) ω) := by
  have hm := progressive_clamp_measurable hf T
  exact hm.comp_measurable (measurable_real_toNNReal.prodMk measurable_const)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Bounded progressive processes have locally integrable clamped paths; this
uses no completion or exceptional-path replacement. -/
theorem clamped_path_locallyIntegrable (hf : IsStronglyProgressive 𝓕 f)
    (T : ℝ≥0) (C : ℝ) (hbound : ∀ t ω, ‖f t ω‖ ≤ C) (ω : Ω) :
    LocallyIntegrable (fun s : ℝ => f (min s.toNNReal T) ω) volume := by
  apply (locallyIntegrable_const (c := C) : LocallyIntegrable (fun _ : ℝ => C) volume).mono
    (clamped_path_stronglyMeasurable hf T ω).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun s => (hbound _ _).trans (le_abs_self C))

omit mΩ [CompleteSpace E] in
/-- Derivatives of the true Lebesgue primitive recover backward averages at
positive times; no stochastic convergence hypothesis is assumed. -/
theorem pastAverage_tendsto_of_hasDerivAt
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0)) (hpos : ∀ n, 0 < δ n)
    (t : ℝ≥0) (ht : 0 < t) (ω : Ω)
    (hd : HasDerivAt (fun x : ℝ => ∫ s in (0 : ℝ)..x, f s.toNNReal ω) (f t ω) t) :
    Tendsto (fun n => pastAverage (δ n) f t ω) atTop (𝓝 (f t ω)) := by
  have hreal : Tendsto (fun n => (δ n : ℝ)) atTop (𝓝 0) := by
    exact_mod_cast NNReal.continuous_coe.continuousAt.tendsto.comp hδ
  have hshift : Tendsto (fun n => (t : ℝ) - δ n) atTop (𝓝[≠] (t : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using tendsto_const_nhds.sub hreal
    · exact Filter.Eventually.of_forall (fun n => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have hp : (0 : ℝ) < δ n := by exact_mod_cast hpos n
        linarith)
  have hlim := hd.tendsto_slope.comp hshift
  apply hlim.congr'
  have he : ∀ᶠ n in atTop, δ n < t := hδ.eventually_lt_const ht
  filter_upwards [he] with n hn
  unfold pastAverage primitive
  rw [NNReal.coe_sub hn.le]
  rw [← intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    ← intervalIntegral.integral_of_le (sub_nonneg.mpr (show (δ n : ℝ) ≤ t by exact_mod_cast hn.le))]
  simp only [Function.comp_apply, slope, vsub_eq_sub, sub_sub_cancel_left, inv_neg,
    neg_smul, ← smul_neg, neg_sub]

def averagingScale (n : ℕ) : ℝ≥0 := 1 / (n + 1 : ℝ≥0)

theorem averagingScale_pos (n : ℕ) : 0 < averagingScale n := by
  unfold averagingScale
  positivity

theorem averagingScale_tendsto : Tendsto averagingScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def predictableRepresentative (f : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : E :=
  limUnder atTop (fun n => pastAverage (averagingScale n) f t ω)

theorem representative_predictable (hf : IsStronglyProgressive 𝓕 f)
    (hi : ∀ ω, LocallyIntegrable (fun s : ℝ => f s.toNNReal ω) volume) :
    IsStronglyPredictable 𝓕 (predictableRepresentative f) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  change StronglyMeasurable (fun z : ℝ≥0 × Ω =>
    limUnder atTop (fun n => pastAverage (averagingScale n) f z.1 z.2))
  apply StronglyMeasurable.limUnder
  exact fun n => pastAverage_predictable hf hi (averagingScale n)

omit mΩ in
/-- Lebesgue differentiation yields the actual representative equality for
almost every time, for each fixed path. -/
theorem representative_ae_time
    (hi : ∀ ω, LocallyIntegrable (fun s : ℝ => f s.toNNReal ω) volume)
    (T : ℝ≥0) (ω : Ω) :
    ∀ᵐ t ∂(CommonItoCLM.timeMeasure_T T), predictableRepresentative f t ω = f t ω := by
  have hd := _root_.LocallyIntegrable.ae_hasDerivAt_integral (hi ω)
  have hd' := (RealTimeBridge.coe_measurePreserving T).quasiMeasurePreserving.ae
    (hd.filter_mono (ae_restrict_le (s := Ioc 0 (T : ℝ))))
  have ht : ∀ᵐ t ∂(CommonItoCLM.timeMeasure_T T), 0 < t :=
    (ae_restrict_mem measurableSet_Ioc).mono (fun _ h => h.1)
  filter_upwards [hd', ht] with t hd ht
  apply Filter.Tendsto.limUnder_eq
  apply pastAverage_tendsto_of_hasDerivAt averagingScale averagingScale_tendsto
    averagingScale_pos t ht ω
  simpa using hd 0

/-- The equality is under the actual product measure, not merely a separate
family of time-null sets without a measurable Fubini argument. -/
theorem representative_ae_product (μ : Measure Ω) [SFinite μ]
    (hf : IsStronglyProgressive 𝓕 f)
    (hm : StronglyMeasurable (Function.uncurry f))
    (hi : ∀ ω, LocallyIntegrable (fun s : ℝ => f s.toNNReal ω) volume)
    (T : ℝ≥0) :
    Function.uncurry (predictableRepresentative f) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ]
      Function.uncurry f := by
  have hg := (representative_predictable hf hi).mono 𝓕.predictable_le_prod
  have he := hg.measurableSet_eq_fun hm
  apply (ae_prod_iff_ae_ae he).mpr
  apply (ae_ae_comm he).mpr
  exact Filter.Eventually.of_forall (representative_ae_time hi T)

/-- Every bounded progressive process has a genuine predictable representative
on each finite horizon. The construction uses past averages and differentiation. -/
theorem exists_predictable_bounded (μ : Measure Ω) [SFinite μ]
    (hf : IsStronglyProgressive 𝓕 f)
    (C : ℝ) (hbound : ∀ t ω, ‖f t ω‖ ≤ C) (T : ℝ≥0) :
    ∃ g : ℝ≥0 → Ω → E, IsStronglyPredictable 𝓕 g ∧
      Function.uncurry g =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry f := by
  let F : ℝ≥0 → Ω → E := fun t ω => f (min t T) ω
  have hp : IsStronglyProgressive 𝓕 F := progressive_clamp hf T
  have hm : StronglyMeasurable (Function.uncurry F) :=
    (progressive_clamp_measurable hf T).mono (by
      exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (𝓕.le T)))
  have hi : ∀ ω, LocallyIntegrable (fun s : ℝ => F s.toNNReal ω) volume :=
    clamped_path_locallyIntegrable hf T C hbound
  refine ⟨predictableRepresentative F, representative_predictable hp hi, ?_⟩
  apply (representative_ae_product μ hp hm hi T).trans
  have ht : ∀ᵐ t ∂(CommonItoCLM.timeMeasure_T T), t ≤ T :=
    (ae_restrict_mem measurableSet_Ioc).mono (fun _ h => h.2)
  filter_upwards [quasiMeasurePreserving_fst.ae ht] with z hz
  change f (min z.1 T) z.2 = f z.1 z.2
  rw [min_eq_left hz]

/-- Continuous bounded approximations; the norm bound grows while the
approximation tends pointwise to the identity. -/
def boundedApprox (n : ℕ) (x : E) : E :=
  ((n + 1 : ℝ) / ((n + 1 : ℝ) + ‖x‖)) • x

omit mΩ [CompleteSpace E] in
theorem boundedApprox_continuous (n : ℕ) : Continuous (boundedApprox (E := E) n) := by
  unfold boundedApprox
  apply (continuous_const.div (continuous_const.add continuous_norm) ?_).smul continuous_id
  intro x
  exact ne_of_gt (add_pos_of_pos_of_nonneg (by positivity) (norm_nonneg x))

omit mΩ [CompleteSpace E] in
theorem boundedApprox_bound (n : ℕ) (x : E) : ‖boundedApprox n x‖ ≤ (n + 1 : ℝ) := by
  have ha : (0 : ℝ) < n + 1 := by positivity
  have hd : (0 : ℝ) < (n + 1 : ℝ) + ‖x‖ := by positivity
  rw [boundedApprox, norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg ha.le hd.le),
    div_mul_eq_mul_div, div_le_iff₀ hd]
  nlinarith [norm_nonneg x]

omit mΩ [CompleteSpace E] in
theorem boundedApprox_tendsto (x : E) : Tendsto (fun n => boundedApprox n x) atTop (𝓝 x) := by
  have hinv : Tendsto (fun n : ℕ => (n + 1 : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcoef : Tendsto (fun n : ℕ => ((1 : ℝ) + (n + 1 : ℝ)⁻¹ * ‖x‖)⁻¹)
      atTop (𝓝 1) := by
    simpa only [zero_mul, add_zero, inv_one] using
      (tendsto_const_nhds.add (hinv.mul tendsto_const_nhds)).inv₀ (by norm_num : (1 : ℝ) + 0 * ‖x‖ ≠ 0)
  have he (n : ℕ) : ((1 : ℝ) + (n + 1 : ℝ)⁻¹ * ‖x‖)⁻¹ =
      (n + 1 : ℝ) / ((n + 1 : ℝ) + ‖x‖) := by
    have ha : (n + 1 : ℝ) ≠ 0 := by positivity
    have hh : (1 : ℝ) + (n + 1 : ℝ)⁻¹ * ‖x‖ = ((n + 1 : ℝ) + ‖x‖) / (n + 1 : ℝ) := by
      field_simp
    rw [hh, inv_div]
  simp_rw [he] at hcoef
  simpa only [one_smul, boundedApprox] using hcoef.smul (tendsto_const_nhds (x := x))

/-- Every strongly progressive Banach-valued process has a predictable
representative for the genuine finite-horizon time-probability product measure.
The proof uses continuous bounded approximations, actual past averages,
Lebesgue differentiation, and measurable Fubini. -/
theorem exists_predictable (μ : Measure Ω) [SFinite μ]
    (hf : IsStronglyProgressive 𝓕 f) (T : ℝ≥0) :
    ∃ g : ℝ≥0 → Ω → E, IsStronglyPredictable 𝓕 g ∧
      Function.uncurry g =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry f := by
  have hprog (n : ℕ) : IsStronglyProgressive 𝓕 (fun t ω => boundedApprox n (f t ω)) :=
    fun t => (boundedApprox_continuous n).comp_stronglyMeasurable (hf t)
  choose g hp hg using fun n => exists_predictable_bounded μ (hprog n) (n + 1 : ℝ)
    (fun t ω => boundedApprox_bound n (f t ω)) T
  let G : ℝ≥0 → Ω → E := fun t ω => limUnder atTop (fun n => g n t ω)
  refine ⟨G, ?_, ?_⟩
  · letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
    exact StronglyMeasurable.limUnder hp
  · filter_upwards [ae_all_iff.mpr hg] with z hz
    change limUnder atTop (fun n => g n z.1 z.2) = f z.1 z.2
    apply Filter.Tendsto.limUnder_eq
    apply (boundedApprox_tendsto (f z.1 z.2)).congr
    intro n
    exact (hz n).symm

/-- The representative lands in the actual trimmed predictable Lp space used
by the Itô operator, preserving the original process almost everywhere. -/
theorem exists_predictable_Lp (μ : Measure Ω) [SFinite μ]
    (hf : IsStronglyProgressive 𝓕 f) (T : ℝ≥0) (p : ℝ≥0∞)
    (hLp : MemLp (Function.uncurry f) p ((CommonItoCLM.timeMeasure_T T).prod μ)) :
    ∃ g : Lp E p (((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod),
      (g : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry f := by
  obtain ⟨g,hg,hge⟩ := exists_predictable μ hf T
  have hgm : MemLp (Function.uncurry g) p ((CommonItoCLM.timeMeasure_T T).prod μ) :=
    (memLp_congr_ae hge).mpr hLp
  have hgt : MemLp (Function.uncurry g) p
      (((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod) := by
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_trim 𝓕.predictable_le_prod hg]
    exact hgm.2
  refine ⟨hgt.toLp (Function.uncurry g), ?_⟩
  exact (ae_eq_of_ae_eq_trim (MemLp.coeFn_toLp hgt)).trans hge

/-- In a second-countable normed target, the usual progressive-measurability
hypothesis suffices; no extra strong-measurability premise is imposed. -/
theorem exists_predictable_Lp_of_progressive [MeasurableSpace E]
    [SecondCountableTopology E] [OpensMeasurableSpace E]
    (μ : Measure Ω) [SFinite μ] (hf : IsProgressive 𝓕 f) (T : ℝ≥0) (p : ℝ≥0∞)
    (hLp : MemLp (Function.uncurry f) p ((CommonItoCLM.timeMeasure_T T).prod μ)) :
    ∃ g : Lp E p (((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod),
      (g : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry f :=
  exists_predictable_Lp μ hf.isStronglyProgressive T p hLp

#print axioms exists_predictable
#print axioms exists_predictable_Lp_of_progressive
end LinearStochastic.ProgressivePredictable
