module

public import LinearStochastic.CommonStateS2
public import LinearStochastic.ProgressivePredictable

@[expose] public section

/-! A genuine progressive continuous S² process determines the predictable H²
class used by Picard. Joint measurability comes from progressiveness of the
stopped process; no separate-time measurability shortcut is used. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonProcessSpace
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open CommonVectorPicard CommonItoL2 CommonItoCLM ContinuousDoobL2
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

omit [IsProbabilityMeasure μ] in
/-- Genuine progressiveness provides joint measurability under the stopped
product measure, even if no global uncurry measurability was supplied. -/
theorem progressive_spacetime_measurable [SFinite μ] {E : Type*} [NormedAddCommGroup E]
    {R : ℝ≥0 → Ω → E} (hR : IsStronglyProgressive 𝓕 R) (T : ℝ≥0) :
    AEStronglyMeasurable (Function.uncurry R) ((timeMeasure_T T).prod μ) := by
  have hs : StronglyMeasurable (fun z : ℝ≥0 × Ω ↦ R (min z.1 T) z.2) :=
    (ProgressivePredictable.progressive_clamp_measurable hR T).mono (sup_le_sup le_rfl (MeasurableSpace.comap_mono (𝓕.le T)))
  have ht : ∀ᵐ t ∂timeMeasure_T T, t ≤ T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
  apply hs.aestronglyMeasurable.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ht] with z hz
  exact congrArg (fun t ↦ R t z.2) (min_eq_left hz)

/-- An actual S² maximal bound yields square integrability on time×probability. -/
theorem spacetime_memLp_of_s2 {E : Type*} [NormedAddCommGroup E]
    {R : ℝ≥0 → Ω → E} (hR : IsStronglyProgressive 𝓕 R) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ R t ω) (Iic T))
    (h2 : MemLp (pathSup R T) 2 μ) :
    MemLp (Function.uncurry R) 2 ((timeMeasure_T T).prod μ) := by
  have ht : ∀ᵐ t ∂timeMeasure_T T, t ≤ T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
  apply (h2.comp_snd (timeMeasure_T T)).mono' (progressive_spacetime_measurable hR T)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ht,
    Measure.quasiMeasurePreserving_snd.ae hc] with z ht hc
  have hcomp : IsCompact (Iic T) := by rw [← Icc_bot]; exact isCompact_Icc
  have hb : BddAbove (range (fun t : Iic T ↦ ‖R t.val z.2‖)) := by
    simpa only [image_eq_range] using hcomp.bddAbove_image hc.norm
  exact le_ciSup hb ⟨z.1,ht⟩

omit [IsProbabilityMeasure μ] in
/-- Each actual endpoint is square integrable, for use as the random initial
condition of a following interval. -/
theorem eval_memLp_of_s2 {E : Type*} [NormedAddCommGroup E]
    {R : ℝ≥0 → Ω → E} (hR : StronglyAdapted 𝓕 R) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ R t ω) (Iic T))
    (h2 : MemLp (pathSup R T) 2 μ) {t : ℝ≥0} (ht : t ≤ T) : MemLp (R t) 2 μ := by
  apply h2.mono' ((hR t).mono (𝓕.le t)).aestronglyMeasurable
  filter_upwards [hc] with ω hc
  have hcomp : IsCompact (Iic T) := by rw [← Icc_bot]; exact isCompact_Icc
  have hb : BddAbove (range (fun s : Iic T ↦ ‖R s.val ω‖)) := by
    simpa only [image_eq_range] using hcomp.bddAbove_image hc.norm
  exact le_ciSup hb ⟨t,ht⟩

/-- Every ordinary progressive continuous scalar S² process has an actual
predictable H² representative with the same ambient space-time values. -/
theorem exists_predictable_H2 {R : ℝ≥0 → Ω → ℝ} (hR : IsProgressive 𝓕 R) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ R t ω) (Iic T))
    (h2 : MemLp (pathSup R T) 2 μ) :
    ∃ X : H2 𝓕 μ T, (X : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry R :=
  ProgressivePredictable.exists_predictable_Lp_of_progressive μ hR T 2
    (spacetime_memLp_of_s2 hR.isStronglyProgressive T hc h2)
end LinearStochastic.CommonProcessSpace
