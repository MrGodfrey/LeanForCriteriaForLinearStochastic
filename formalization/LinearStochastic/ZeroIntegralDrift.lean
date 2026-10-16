import LinearStochastic.ZeroIntegralSolution

noncomputable section
namespace LinearStochastic.ZeroIntegralDrift
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators Topology
open CommonItoMultichannel VectorItoProduct LinearDuality ZeroIntegralSolution

section Measurability
variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Actual parameterized Lebesgue primitives are jointly strongly measurable. -/
theorem primitive_stronglyMeasurable (f : ℝ × Ω → E) (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : ℝ × Ω => ∫ t in Ioc 0 z.1, f (t,z.2)) := by
  let q : ((ℝ × Ω) × ℝ) → E := fun z =>
    if 0 < z.2 ∧ z.2 ≤ z.1.1 then f (z.2,z.1.2) else 0
  have hq : StronglyMeasurable q := by
    apply (hf.comp_measurable (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).piecewise
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))
    · exact stronglyMeasurable_zero
  have hi := hq.integral_prod_right' (ν := (volume : Measure ℝ))
  convert hi using 1
  funext z
  rw [←integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [q,Set.indicator_apply,Set.mem_Ioc]

/-- Product a.e. zero and interval a.e. zero agree for a genuine measurable
primitive; no exchange of two uncountable null-set families is assumed. -/
theorem drift_zero_of_primitive_sections (T : ℝ) (hT : 0 < T)
    (μ : Measure Ω) [SFinite μ] (f : ℝ × Ω → E) (hf : StronglyMeasurable f)
    (hi : Integrable f ((volume.restrict (Ioc 0 T)).prod μ))
    (hz : ∀ᵐ t ∂volume.restrict (Ioc 0 T), ∀ᵐ ω ∂μ, (∫ s in Ioc 0 t, f (s,ω)) = 0) :
    f =ᵐ[(volume.restrict (Ioc 0 T)).prod μ] 0 := by
  have hm := primitive_stronglyMeasurable f hf
  have hzm : MeasurableSet {z : ℝ × Ω | (∫ s in Ioc 0 z.1, f (s,z.2)) = 0} :=
    by simpa only [norm_eq_zero] using
      measurableSet_eq_fun hm.norm.measurable (measurable_const (a := (0 : ℝ)))
  have hzswap : ∀ᵐ ω ∂μ, ∀ᵐ t ∂volume.restrict (Ioc 0 T), (∫ s in Ioc 0 t, f (s,ω)) = 0 :=
    (Measure.ae_ae_comm hzm).mp hz
  have hout : ∀ᵐ ω ∂μ, ∀ᵐ t ∂volume.restrict (Ioc 0 T), f (t,ω) = 0 := by
    filter_upwards [hzswap,hi.prod_left_ae] with ω hω hiω
    exact drift_zero_of_primitive_zero T hT (fun s => f (s,ω)) hiω hω
  have hfm : MeasurableSet {z : ℝ × Ω | f z = 0} := by
    simpa only [norm_eq_zero] using
      measurableSet_eq_fun hf.norm.measurable (measurable_const (a := (0 : ℝ)))
  apply (Measure.ae_prod_iff_ae_ae hfm).mpr
  exact (Measure.ae_ae_comm hfm).mpr hout
end Measurability

section Stochastic
variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

omit [CompleteSpace E] in
/-- The chosen stochastic-integral representative of zero is zero at every
fixed time almost surely; no false pointwise representative equality is used. -/
theorem vectorProcess_zero_ae (T t : ℝ≥0) :
    vectorProcess (𝓕 := 𝓕) b hW hWm T (fun _ => 0) t =ᵐ[μ] 0 := by
  have hc (a : κ) : coordinate b a (0 : Lp E 2 (spacetimeMeasure 𝓕 μ T)) = 0 := by
    simp only [coordinate,ContinuousLinearMap.compLp,LipschitzWith.compLp_zero]
  have hz (i : ι) : CommonItoMartingaleVersion.integralProcess (hW i) T (hWm i)
      (0 : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) t =ᵐ[μ] 0 := by
    have h := CommonItoMartingaleVersion.integralProcess_ae_eq (hW i) T t (hWm i)
      (0 : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T))
    have hmap : CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i)
        (0 : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) = 0 := map_zero _
    rw [hmap] at h
    exact h.trans (Lp.coeFn_zero ℝ 2 μ)
  have hzall : ∀ᵐ ω ∂μ, ∀ i, CommonItoMartingaleVersion.integralProcess (hW i) T (hWm i)
      (0 : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) t ω = 0 := by
    rw [ae_all_iff]
    exact hz
  filter_upwards [hzall] with ω hω
  simp only [vectorProcess,ItoExpectedProduct.sumProcess,hc,hω,Finset.sum_const_zero,zero_smul,Pi.zero_apply]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The predictable L² zero class is zero after the actual change from the
nonnegative clock to the manuscript's real spacetime measure. -/
theorem real_zero_ae (T : ℝ≥0) :
    (fun z : ℝ × Ω => (0 : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (z.1.toNNReal,z.2))
      =ᵐ[(volume.restrict (Ioc 0 (T : ℝ))).prod μ] 0 := by
  have hz := ae_eq_of_ae_eq_trim (hm := 𝓕.predictable_le_prod)
    (Lp.coeFn_zero E 2 (spacetimeMeasure 𝓕 μ T))
  exact ((RealTimeBridge.toNNReal_measurePreserving T).prod (MeasurePreserving.id μ)).quasiMeasurePreserving.ae_eq_comp hz

omit [CompleteSpace E] in
/-- Real-spacetime almost-everywhere zero is the actual zero predictable L²
class, established through the already proved covariance transport. -/
theorem predictable_zero_of_real_ae (T : ℝ≥0) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hf : (fun z : ℝ × Ω => f (z.1.toNNReal,z.2))
      =ᵐ[(volume.restrict (Ioc 0 (T : ℝ))).prod μ] 0) : f = 0 := by
  have hi : inner ℝ f f = 0 := by
    rw [predictable_inner_real_vector]
    apply integral_eq_zero_of_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hf] with t ht
    apply integral_eq_zero_of_ae
    filter_upwards [ht] with ω hω
    simp only [Pi.zero_apply] at hω
    rw [hω,inner_zero_left]
    rfl
  rw [real_inner_self_eq_norm_sq] at hi
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)

/-- Both components of a genuine zero Itô decomposition vanish. The drift
conclusion uses Fubini only after proving joint primitive measurability. -/
theorem zero_decomposition
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (hT : 0 < T) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hzero : IntegralSolution b hW hWm T 0 f φ 0 0) :
    f = 0 ∧ ∀ i, φ i = 0 := by
  have hφ := diffusion_zero_of_zero_solution b hW hWm hpair hchannels T f φ hzero
  have hφeq : φ = fun _ => 0 := funext hφ
  refine ⟨?_,hφ⟩
  have hspace := hzero.spacetime
  rw [hφeq] at hspace
  have hz := (real_zero_ae (𝓕 := 𝓕) (E := E) T).symm.trans hspace
  let F : ℝ × Ω → E := fun z => f (z.1.toNNReal,z.2)
  have hF : StronglyMeasurable F :=
    ((Lp.stronglyMeasurable f).mono 𝓕.predictable_le_prod).comp_measurable
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hFi : Integrable F ((volume.restrict (Ioc 0 (T : ℝ))).prod μ) :=
    (RealTimeBridge.predictable_memLp_real_extension T μ 𝓕 f).integrable one_le_two
  have hprim : ∀ᵐ t ∂volume.restrict (Ioc 0 (T : ℝ)), ∀ᵐ ω ∂μ,
      (∫ s in Ioc 0 t, F (s,ω)) = 0 := by
    filter_upwards [Measure.ae_ae_of_ae_prod hz] with t ht
    filter_upwards [ht,vectorProcess_zero_ae (𝓕 := 𝓕) b hW hWm T t.toNNReal] with ω hω hito
    simp only [Function.uncurry,integralState,Pi.zero_apply] at hω hito
    simpa only [F,hito,zero_add,add_zero] using hω.symm
  apply predictable_zero_of_real_ae T f
  exact drift_zero_of_primitive_sections T (by exact_mod_cast hT) μ F hF hFi hprim
end Stochastic

#print axioms zero_decomposition
end LinearStochastic.ZeroIntegralDrift
