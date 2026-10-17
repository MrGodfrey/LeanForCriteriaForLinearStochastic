module

public import LinearStochastic.CommonShiftMeasure

@[expose] public section

/-! The actual predictable L² restriction/translation operator for deterministic
restarts. It is built from real spacetime transport and the proved progressive
representative theorem; its representative, linearity and norm bound are proved. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonShiftH2
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open CommonItoL2 CommonItoCLM
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

abbrev Space (𝓕 : Filtration ℝ≥0 mΩ) (μ : Measure Ω) (T : ℝ≥0) :=
  Lp ℝ 2 (((timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod)

omit [SFinite μ] in
theorem ambient_memLp (T : ℝ≥0) (f : Space 𝓕 μ T) :
    MemLp (f : ℝ≥0 × Ω → ℝ) 2 ((timeMeasure_T T).prod μ) :=
  by
    unfold MemLp
    rw [←eLpNorm_trim_ae 𝓕.predictable_le_prod (Lp.aestronglyMeasurable f)]
    exact Lp.memLp f

def shift (a δ T : ℝ≥0) (h : a+δ ≤ T) (f : Space 𝓕 μ T) :
    Space (CommonTimeShift.filtration 𝓕 a) μ δ :=
  (CommonShiftMeasure.exists_shifted_predictable μ 𝓕 a δ T h
    (fun t ω ↦ f (t,ω))
    ((show IsStronglyPredictable 𝓕 (fun t ω ↦ f (t,ω)) from Lp.stronglyMeasurable f).isStronglyProgressive.isProgressive)
    (ambient_memLp T f)).choose

theorem shift_ae (a δ T : ℝ≥0) (h : a+δ ≤ T) (f : Space 𝓕 μ T) :
    (shift a δ T h f : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T δ).prod μ]
      (fun z ↦ f (a+z.1,z.2)) :=
  (CommonShiftMeasure.exists_shifted_predictable μ 𝓕 a δ T h
    (fun t ω ↦ f (t,ω))
    ((show IsStronglyPredictable 𝓕 (fun t ω ↦ f (t,ω)) from Lp.stronglyMeasurable f).isStronglyProgressive.isProgressive)
    (ambient_memLp T f)).choose_spec

theorem pull_ae (a δ T : ℝ≥0) (h : a+δ ≤ T)
    {f g : ℝ≥0 × Ω → ℝ} (he : f =ᵐ[(timeMeasure_T T).prod μ] g) :
    (fun z : ℝ≥0 × Ω ↦ f (a+z.1,z.2)) =ᵐ[(timeMeasure_T δ).prod μ]
      (fun z ↦ g (a+z.1,z.2)) :=
  ((CommonShiftMeasure.add_interval a δ).prod (MeasurePreserving.id μ)).quasiMeasurePreserving.ae
    (he.filter_mono (ae_mono (Measure.prod_mono (CommonShiftMeasure.interval_le a δ T h) le_rfl)))

theorem shift_add (a δ T : ℝ≥0) (h : a+δ ≤ T) (f g : Space 𝓕 μ T) :
    shift a δ T h (f+g) = shift a δ T h f + shift a δ T h g := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
    (CommonTimeShift.filtration 𝓕 a).predictable_le_prod (Lp.stronglyMeasurable _)
  filter_upwards [shift_ae a δ T h (f+g),shift_ae a δ T h f,shift_ae a δ T h g,
    pull_ae a δ T h (ae_of_ae_trim 𝓕.predictable_le_prod (Lp.coeFn_add f g)),
    ae_of_ae_trim (CommonTimeShift.filtration 𝓕 a).predictable_le_prod
      (Lp.coeFn_add (shift a δ T h f) (shift a δ T h g))] with z hs hf hg hadd hout
  rw [hs,hadd,hout]
  simp only [Pi.add_apply,hf,hg]

theorem shift_smul (a δ T : ℝ≥0) (h : a+δ ≤ T) (c : ℝ) (f : Space 𝓕 μ T) :
    shift a δ T h (c • f) = c • shift a δ T h f := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
    (CommonTimeShift.filtration 𝓕 a).predictable_le_prod (Lp.stronglyMeasurable _)
  filter_upwards [shift_ae a δ T h (c • f),shift_ae a δ T h f,
    pull_ae a δ T h (ae_of_ae_trim 𝓕.predictable_le_prod (Lp.coeFn_smul c f)),
    ae_of_ae_trim (CommonTimeShift.filtration 𝓕 a).predictable_le_prod
      (Lp.coeFn_smul c (shift a δ T h f))] with z hs hf hsm hout
  rw [hs,hsm,hout]
  simp only [Pi.smul_apply,hf]

theorem shift_norm (a δ T : ℝ≥0) (h : a+δ ≤ T) (f : Space 𝓕 μ T) :
    ‖shift a δ T h f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def,Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.memLp f).eLpNorm_lt_top.ne
  rw [eLpNorm_trim_ae _ (Lp.aestronglyMeasurable _),eLpNorm_congr_ae (shift_ae a δ T h f)]
  have hs := (ambient_memLp T f).mono_measure
    (Measure.prod_mono (CommonShiftMeasure.interval_le a δ T h) le_rfl)
  change eLpNorm ((f : ℝ≥0 × Ω → ℝ) ∘ Prod.map (fun t ↦ a+t) id) 2 _ ≤ _
  rw [eLpNorm_comp_measurePreserving hs.aestronglyMeasurable ((CommonShiftMeasure.add_interval a δ).prod (MeasurePreserving.id μ)),
    eLpNorm_trim_ae _ (Lp.aestronglyMeasurable f)]
  exact eLpNorm_mono_measure f (Measure.prod_mono (CommonShiftMeasure.interval_le a δ T h) le_rfl)

/-- Genuine restart restriction as a continuous linear contraction. -/
def shiftCLM (a δ T : ℝ≥0) (h : a+δ ≤ T) :
    Space 𝓕 μ T →L[ℝ] Space (CommonTimeShift.filtration 𝓕 a) μ δ :=
  LinearMap.mkContinuous
    { toFun := shift a δ T h
      map_add' := shift_add a δ T h
      map_smul' := shift_smul a δ T h } 1
    (by intro f; change ‖shift a δ T h f‖ ≤ 1 * ‖f‖; simpa only [one_mul] using shift_norm a δ T h f)
end LinearStochastic.CommonShiftH2
