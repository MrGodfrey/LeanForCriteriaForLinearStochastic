module

public import LinearStochastic.PredictableConstant
public import LinearStochastic.VectorH2Extension
public import LinearStochastic.DiffusionKernelWitness
public import LinearStochastic.VectorItoNaturality

@[expose] public section

/-! Actual normalized predictable diffusion spikes on a terminal time window.
Their exact L² energy, adjoint-control kernel identity, and stochastic terminal
norm are proved for the constructed common-filtration Itô integral. -/
noncomputable section
set_option maxHeartbeats 800000
namespace LinearStochastic.TerminalSpikeNoise
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct VectorItoNaturality PredictableConstant
variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace E] [CompleteSpace U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hWm : ∀ i t, Measurable (W i t)) (i₀ : ι)

/-- The real input is a constant in the restarted predictable space, transported
by the proved isometric zero extension on the original probability space. -/
def noise (a δ T : ℝ≥0) (h : a+δ ≤ T) (q : ι → E) :
    ι → Lp E 2 (spacetimeMeasure 𝓕 μ T) := fun i ↦
  VectorH2Extension.extendShift b (hWm i₀) a δ T h
    (constant (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ ((Real.sqrt (δ:ℝ))⁻¹ • q i))

omit [CompleteSpace E] in
/-- Exact joint energy: the normalization uses the actual interval length. -/
theorem energy (a δ T : ℝ≥0) (h : a+δ ≤ T) (hδ : 0 < δ) (q : ι → E) :
    ∑ i, ‖noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h q i‖^2 = ∑ i, ‖q i‖^2 := by
  apply Finset.sum_congr rfl
  intro i _
  rw [noise,VectorH2Extension.extendShift_norm,normalized_norm_sq δ hδ]

omit [CompleteSpace E] [Fintype ι] in
/-- Exact pointwise representative on the original time clock, including zero
outside the selected window, modulo ambient product measure. -/
theorem noise_ae (a δ T : ℝ≥0) (h : a+δ ≤ T) (q : ι → E) (i : ι) :
    (noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h q i : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ]
      fun z ↦ if a < z.1 ∧ z.1 ≤ a+δ then (Real.sqrt (δ:ℝ))⁻¹ • q i else 0 := by
  have hc := ae_of_ae_trim (CommonTimeShift.filtration 𝓕 a).predictable_le_prod
    (constant_ae (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ ((Real.sqrt (δ:ℝ))⁻¹ • q i))
  have hw := VectorH2Extension.window_ae (μ:=μ) a δ T h
    (fun z ↦ constant (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ ((Real.sqrt (δ:ℝ))⁻¹ • q i) z =
      (Real.sqrt (δ:ℝ))⁻¹ • q i) hc
  filter_upwards [VectorH2Extension.extendShift_ae b (hWm i₀) a δ T h
    (constant (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ ((Real.sqrt (δ:ℝ))⁻¹ • q i)),hw]
    with z he hw
  rw [show noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h q i z = _ from he]
  split_ifs with hz
  · exact hw hz
  · rfl

/-- The diffusion contribution to the actual adjoint observation is zero,
because the genuine full-channel kernel equation is zero. -/
theorem observation_zero (a δ T : ℝ≥0) (h : a+δ ≤ T) (q : ι → E)
    (D : ι → U →L[ℝ] E) (hq : ∑ i, (D i).adjoint (q i) = 0) :
    ∑ i, (D i).adjoint.compLp (noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h q i) = 0 := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable 𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
  have hc : ∀ᵐ z ∂(CommonItoCLM.timeMeasure_T T).prod μ, ∀ i,
      (D i).adjoint.compLp (noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h q i) z =
      (D i).adjoint (if a < z.1 ∧ z.1 ≤ a+δ then (Real.sqrt (δ:ℝ))⁻¹ • q i else 0) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod
      ((D i).adjoint.coeFn_compLp (noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h q i)),noise_ae (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h q i]
      with z hL hz
    rw [hL,hz]
  filter_upwards [hc,ae_of_ae_trim 𝓕.predictable_le_prod
    (Lp.coeFn_finsetSum Finset.univ (fun i ↦ (D i).adjoint.compLp (noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h q i))),
    ae_of_ae_trim 𝓕.predictable_le_prod (Lp.coeFn_zero U 2 (spacetimeMeasure 𝓕 μ T))] with z hc hs hz
  rw [hs,hz]
  simp only [Finset.sum_apply,hc]
  by_cases ht : a < z.1 ∧ z.1 ≤ a+δ
  · simp only [if_pos ht,map_smul,←Finset.smul_sum,hq,smul_zero,Pi.zero_apply]
  · simp only [if_neg ht,map_zero,Finset.sum_const_zero,Pi.zero_apply]

omit [CompleteSpace E] in
/-- The actual stochastic terminal of a unit joint spike has exactly unit L²
norm, using proved channel orthogonality, not a covariance premise. -/
theorem stochastic_norm (hW : ∀ i, IsPreBrownianReal (W i) μ)
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (a δ T : ℝ≥0) (h : a+δ ≤ T) (hδ : 0 < δ) (q : ι → E)
    (hq : ∑ i, ‖q i‖^2 = 1) :
    ‖vectorLp b hW hWm T T (noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h q)‖ = 1 := by
  have he := vectorProcess_terminal_inner b hW hWm hpair hchannels T
    (noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h q) (noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h q)
  have hh : ‖vectorLp b hW hWm T T (noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h q)‖^2 = 1 := by
    rw [←real_inner_self_eq_norm_sq,L2.inner_def]
    rw [integral_congr_ae ((vectorProcess_ae_vectorLp b hW hWm T T
      (noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h q)).symm.mono (fun ω hω ↦ by rw [hω]))]
    rw [he]
    simp only [real_inner_self_eq_norm_sq]
    exact (energy (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h hδ q).trans hq
  nlinarith [norm_nonneg (vectorLp b hW hWm T T (noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ T h q))]
end LinearStochastic.TerminalSpikeNoise
