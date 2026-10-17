module

public import LinearStochastic.RealTimeBridge
public import LinearStochastic.CommonItoMultichannel
public import LinearStochastic.CommonItoMartingaleVersion

@[expose] public section

/-! Actual finite-channel Itô processes and their expected product on the
manuscript's real Lebesgue time interval. -/
noncomputable section
namespace LinearStochastic.ItoExpectedProduct
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonItoMartingaleVersion

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ι : Type*} [Fintype ι] {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- The finite sum of genuine adapted versions of the constructed Itô integrals. -/
def sumProcess (T : ℝ≥0) (f : ι → Lp ℝ 2 (spacetimeMeasure 𝓕 μ T))
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i, integralProcess (hW i) T (hWm i) (f i) t ω

theorem sumProcess_martingale (T : ℝ≥0)
    (f : ι → Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    Martingale (sumProcess hW hWm T f) 𝓕 μ := by
  classical
  have hs (s : Finset ι) : Martingale
      (fun t ω => ∑ i ∈ s, integralProcess (hW i) T (hWm i) (f i) t ω) 𝓕 μ := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact martingale_zero ℝ 𝓕 μ
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (integralProcess_martingale (hW i) T (hWm i) (f i)).add ih
  exact hs Finset.univ

theorem sumProcess_memLp (T t : ℝ≥0)
    (f : ι → Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    MemLp (sumProcess hW hWm T f t) 2 μ := by
  exact memLp_finsetSum Finset.univ
    (fun i _ => integralProcess_memLp (hW i) T t (hWm i) (f i))

theorem sumProcess_terminal_ae (T : ℝ≥0)
    (f : ι → Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    sumProcess hW hWm T f T =ᵐ[μ] (sumIntegral hW hWm T f : Ω → ℝ) := by
  have h : ∀ᵐ ω ∂μ, ∀ i, integralProcess (hW i) T (hWm i) (f i) T ω =
      channelIntegral hW hWm i T (f i) ω := by
    rw [ae_all_iff]
    exact fun i => integralProcess_terminal_ae (hW i) T (hWm i) (f i)
  filter_upwards [h, Lp.coeFn_fun_finsetSum Finset.univ
    (fun i => channelIntegral hW hWm i T (f i))] with ω hω hsum
  exact (Finset.sum_congr rfl (fun i _ => hω i)).trans hsum.symm

/-- The terminal covariance is derived from actual channel integrals and their
independence, not supplied as a martingale covariance assumption. -/
theorem sumProcess_terminal_inner
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (f g : ι → Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    (∫ ω, inner ℝ (sumProcess hW hWm T f T ω) (sumProcess hW hWm T g T ω) ∂μ) =
      ∑ i, inner ℝ (f i) (g i) := by
  calc
    _ = inner ℝ (sumIntegral hW hWm T f) (sumIntegral hW hWm T g) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [sumProcess_terminal_ae hW hWm T f,
        sumProcess_terminal_ae hW hWm T g] with ω hf hg
      rw [hf,hg]
    _ = _ := sumIntegral_inner hW hWm hpair hchannels T f g

/-- The L² inner product on the actual predictable domain is exactly the
iterated Lebesgue-time/sample-space covariance. Integrability is derived before
Fubini is used. -/
theorem predictable_inner_real (T : ℝ≥0)
    (f g : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    inner ℝ f g = ∫ s in Ioc 0 (T : ℝ),
      ∫ ω, inner ℝ (f (s.toNNReal,ω)) (g (s.toNNReal,ω)) ∂μ := by
  have hi : Integrable (fun z => inner ℝ (f z) (g z))
      ((CommonItoCLM.timeMeasure_T T).prod μ) :=
    integrable_of_integrable_trim 𝓕.predictable_le_prod (L2.integrable_inner f g)
  rw [L2.inner_def]
  change (∫ z, inner ℝ (f z) (g z) ∂(((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod)) = _
  rw [← integral_trim (μ := (CommonItoCLM.timeMeasure_T T).prod μ) 𝓕.predictable_le_prod
    ((Lp.stronglyMeasurable f).inner (Lp.stronglyMeasurable g)), integral_prod _ hi]
  exact (RealTimeBridge.integral_real_extension T
    (fun s => ∫ ω, inner ℝ (f (s,ω)) (g (s,ω)) ∂μ)).symm

/-- Actual expected product formula for finite independent Brownian channels,
with arbitrary common-predictable L² drifts and diffusion integrands. All Itô
terms are the continuous extensions of actual finite increment sums. -/
theorem expected_ito_product
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (f g : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T))
    (φ ψ : ι → Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    (∫ ω, inner ℝ
      ((∫ s in Ioc 0 (T : ℝ), f (s.toNNReal,ω)) + sumProcess hW hWm T φ T ω)
      ((∫ s in Ioc 0 (T : ℝ), g (s.toNNReal,ω)) + sumProcess hW hWm T ψ T ω) ∂μ) =
      (∑ i, ∫ s in Ioc 0 (T : ℝ),
        ∫ ω, inner ℝ (φ i (s.toNNReal,ω)) (ψ i (s.toNNReal,ω)) ∂μ) +
      (∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ (f (s.toNNReal,ω))
        ((∫ t in Ioc 0 s, g (t.toNNReal,ω)) + sumProcess hW hWm T ψ s.toNNReal ω) ∂μ) +
      (∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ
        ((∫ t in Ioc 0 s, f (t.toNNReal,ω)) + sumProcess hW hWm T φ s.toNNReal ω)
          (g (s.toNNReal,ω)) ∂μ) := by
  have h := RealTimeBridge.predictable_expected_product T μ 𝓕
    (sumProcess hW hWm T φ) (sumProcess hW hWm T ψ)
    (sumProcess_martingale hW hWm T φ) (sumProcess_martingale hW hWm T ψ)
    (sumProcess_memLp hW hWm T T φ) (sumProcess_memLp hW hWm T T ψ) f g
  refine h.trans ?_
  rw [sumProcess_terminal_inner hW hWm hpair hchannels]
  simp_rw [predictable_inner_real]
  rfl

end LinearStochastic.ItoExpectedProduct
