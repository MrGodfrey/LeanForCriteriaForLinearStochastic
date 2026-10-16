import LinearStochastic.ZeroIntegralDrift
import LinearStochastic.SectionLinearDuality

/-! Decomposition uniqueness for the genuine sectionwise integral-solution
interface; no product measurability of the raw Itô representative is assumed. -/
noncomputable section
namespace LinearStochastic.SectionZeroDecomposition
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators Topology
open CommonItoMultichannel VectorItoProduct LinearDuality ZeroIntegralDrift
open SectionLinearDuality
section Stochastic
variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Diffusion uniqueness for an actual zero integral solution. The Itô energy
identity is derived from the constructed Brownian integral; neither uniqueness
nor zero quadratic variation is supplied as a premise. -/
theorem diffusion_zero_of_zero_solution
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hzero : SectionIntegralSolution b hW hWm T 0 f φ 0 0) : ∀ i, φ i = 0 := by
  have h := SectionLinearDuality.integral_solution_product b hW hWm hpair hchannels T 0 0
    (MemLp.zero) (MemLp.zero) stronglyMeasurable_zero stronglyMeasurable_zero
    f f 0 0 φ φ 0 0 hzero hzero
  simp only [Pi.zero_apply,inner_zero_left,inner_zero_right,integral_zero,
    add_zero,zero_add,real_inner_self_eq_norm_sq] at h
  have hs : ∀ i, ‖φ i‖ ^ 2 = 0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖φ i‖)).mp h.symm
    exact fun i => hh i (Finset.mem_univ i)
  intro i
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hs i))
/-- Both components of a genuine zero Itô decomposition vanish. The drift
conclusion uses Fubini only after proving joint primitive measurability. -/
theorem zero_decomposition
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (hT : 0 < T) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hzero : SectionIntegralSolution b hW hWm T 0 f φ 0 0) :
    f = 0 ∧ ∀ i, φ i = 0 := by
  have hφ := diffusion_zero_of_zero_solution b hW hWm hpair hchannels T f φ hzero
  have hφeq : φ = fun _ => 0 := funext hφ
  refine ⟨?_,hφ⟩
  have hspace := hzero.sections
  rw [hφeq] at hspace
  have hz0 := Measure.ae_ae_of_ae_prod (real_zero_ae (μ := μ) (𝓕 := 𝓕) (E := E) T)
  let F : ℝ × Ω → E := fun z => f (z.1.toNNReal,z.2)
  have hF : StronglyMeasurable F :=
    ((Lp.stronglyMeasurable f).mono 𝓕.predictable_le_prod).comp_measurable
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hFi : Integrable F ((volume.restrict (Ioc 0 (T : ℝ))).prod μ) :=
    (RealTimeBridge.predictable_memLp_real_extension T μ 𝓕 f).integrable one_le_two
  have hprim : ∀ᵐ t ∂volume.restrict (Ioc 0 (T : ℝ)), ∀ᵐ ω ∂μ,
      (∫ s in Ioc 0 t, F (s,ω)) = 0 := by
    filter_upwards [hspace,hz0] with t ht ht0
    filter_upwards [ht,ht0,ZeroIntegralDrift.vectorProcess_zero_ae (𝓕 := 𝓕) b hW hWm T t.toNNReal] with ω hω h0 hito
    simp only [integralState,Pi.zero_apply] at hω hito
    rw [h0] at hω
    simpa only [F,hito,zero_add,add_zero,Pi.zero_apply] using hω.symm
  apply predictable_zero_of_real_ae T f
  exact drift_zero_of_primitive_sections T (by exact_mod_cast hT) μ F hF hFi hprim
end Stochastic
#print axioms zero_decomposition
end LinearStochastic.SectionZeroDecomposition
