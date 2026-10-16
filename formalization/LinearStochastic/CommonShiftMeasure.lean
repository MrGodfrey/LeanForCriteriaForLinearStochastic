import LinearStochastic.CommonTimeShift
import LinearStochastic.RealTimeBridge

/-! Actual measure transport of deterministic restart intervals. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonShiftMeasure
open MeasureTheory Set
open scoped NNReal ENNReal
open CommonItoL2 CommonItoCLM

/-- Inclusion identifies any nonnegative clock interval with real Lebesgue measure. -/
theorem coe_interval (a b : ℝ≥0) :
    MeasurePreserving ((↑) : ℝ≥0 → ℝ) (timeMeasure.restrict (Ioc a b))
      (volume.restrict (Ioc (a:ℝ) (b:ℝ))) := by
  refine ⟨NNReal.continuous_coe.measurable,?_⟩
  have hf := measurableEmbedding_nnrealCoe
  have himg : ((↑) : ℝ≥0 → ℝ) '' Ioc a b = Ioc (a:ℝ) (b:ℝ) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨by exact_mod_cast hy.1,by exact_mod_cast hy.2⟩
    · intro hx
      exact ⟨⟨x,le_trans a.coe_nonneg hx.1.le⟩,
        ⟨by exact_mod_cast hx.1,by exact_mod_cast hx.2⟩,rfl⟩
  rw [timeMeasure,hf.restrict_comap,hf.map_comap,
    Measure.restrict_restrict hf.measurableSet_range,
    inter_eq_right.mpr (image_subset_range _ _),himg]

/-- Translation preserves Lebesgue measure on the exact restart interval. -/
theorem real_add (a T : ℝ) :
    MeasurePreserving (fun t : ℝ ↦ a+t) (volume.restrict (Ioc 0 T))
      (volume.restrict (Ioc a (a+T))) := by
  have h := (measurePreserving_add_left (volume:Measure ℝ) a).restrict_preimage
    (measurableSet_Ioc : MeasurableSet (Ioc a (a+T)))
  have he : (fun t : ℝ ↦ a+t) ⁻¹' Ioc a (a+T) = Ioc 0 T := by
    ext t
    simp only [mem_preimage,mem_Ioc]
    constructor <;> intro h <;> constructor <;> linarith
  rwa [he] at h

/-- The original nonnegative clock, translated onto (a,a+T], has exactly the
original interval measure; no fresh probability space or integrability axiom. -/
theorem add_interval (a T : ℝ≥0) :
    MeasurePreserving (fun t : ℝ≥0 ↦ a+t) (timeMeasure_T T)
      (timeMeasure.restrict (Ioc a (a+T))) := by
  refine ⟨measurable_const.add measurable_id,?_⟩
  apply measurableEmbedding_nnrealCoe.map_injective
  rw [Measure.map_map NNReal.continuous_coe.measurable (show Measurable (fun t : ℝ≥0 ↦ a+t) from measurable_const.add measurable_id)]
  have hc := (real_add (a:ℝ) (T:ℝ)).comp (RealTimeBridge.coe_measurePreserving T)
  simpa only [Function.comp_def,NNReal.coe_add] using hc.map_eq.trans (coe_interval a (a+T)).map_eq.symm

/-- The actual translated interval remains inside the original finite horizon. -/
theorem interval_le (a δ T : ℝ≥0) (h : a+δ ≤ T) :
    timeMeasure.restrict (Ioc a (a+δ)) ≤ timeMeasure_T T := by
  apply Measure.restrict_mono _ le_rfl
  intro t ht
  exact ⟨lt_of_le_of_lt (show 0 ≤ a from zero_le) ht.1,ht.2.trans h⟩

/-- The same raw control, viewed after restart, retains its actual spacetime L²
integrability. The estimate follows from restricted measure monotonicity and
an exact product measure preserving map. -/
theorem shifted_memLp {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) [SFinite μ] (a δ T : ℝ≥0) (h : a+δ ≤ T)
    (R : ℝ≥0 → Ω → E)
    (hR : MemLp (Function.uncurry R) 2 ((timeMeasure_T T).prod μ)) :
    MemLp (fun z : ℝ≥0 × Ω ↦ R (a+z.1) z.2) 2 ((timeMeasure_T δ).prod μ) := by
  have hs := hR.mono_measure (Measure.prod_mono (interval_le a δ T h) le_rfl)
  exact hs.comp_measurePreserving ((add_interval a δ).prod (MeasurePreserving.id μ))

/-- Real Lebesgue primitives transform by the actual deterministic translation. -/
theorem integral_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a T : ℝ≥0) (f : ℝ≥0 → E) :
    (∫ t in Ioc (0:ℝ≥0) T, f (a+t) ∂timeMeasure) =
      ∫ t in Ioc a (a+T), f t ∂timeMeasure := by
  exact (add_interval a T).integral_comp
    ((continuous_const.add continuous_id : Continuous (fun t : ℝ≥0 ↦ a+t)).measurableEmbedding
      (fun _ _ h ↦ add_left_cancel h)) f

/-- An ordinary progressive control on the original horizon has a predictable
L² representative for the restarted filtration on the original sample space. -/
theorem exists_shifted_predictable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (𝓕 : Filtration ℝ≥0 mΩ)
    (a δ T : ℝ≥0) (h : a+δ ≤ T) (R : ℝ≥0 → Ω → ℝ)
    (hprog : IsProgressive 𝓕 R)
    (hR : MemLp (Function.uncurry R) 2 ((timeMeasure_T T).prod μ)) :
    ∃ u : Lp ℝ 2 (((timeMeasure_T δ).prod μ).trim (CommonTimeShift.filtration 𝓕 a).predictable_le_prod),
      (u : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T δ).prod μ] (fun z ↦ R (a+z.1) z.2) :=
  ProgressivePredictable.exists_predictable_Lp_of_progressive μ
    (CommonTimeShift.progressive hprog a) δ 2 (shifted_memLp μ a δ T h R hR)

end LinearStochastic.CommonShiftMeasure
