module

public import LinearStochastic.CommonItoCross

@[expose] public section

noncomputable section
namespace LinearStochastic.CommonItoMultichannel
open MeasureTheory ProbabilityTheory CommonItoCLM CommonItoCross
open scoped NNReal InnerProductSpace BigOperators
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ι : Type*} [Fintype ι] {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- The common predictable spacetime measure for an arbitrary sample space. -/
def spacetimeMeasure (𝓕 : Filtration ℝ≥0 mΩ) (μ : Measure Ω) (T : ℝ≥0) :=
  ((timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod

def channelIntegral (i : ι) (T : ℝ≥0) :
    Lp ℝ 2 (spacetimeMeasure 𝓕 μ T) →L[ℝ] Lp ℝ 2 μ :=
  itoIntegralCLM_T (𝓕:=𝓕) (hW i) T (hWm i)

def sumIntegral (T : ℝ≥0) (f : ι → Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) : Lp ℝ 2 μ :=
  ∑ i, channelIntegral (𝓕:=𝓕) hW hWm i T (f i)

/-- Generic multi-channel bilinear Itô isometry. All assumptions are actual
Brownian laws, measurability and independence of actual processes. There is no
canonical-sample-space restriction, or integral/isometry supplied as a premise. -/
theorem sumIntegral_inner
    (hpair : ∀ i j, PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (f g : ι → Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    ⟪sumIntegral (𝓕:=𝓕) hW hWm T f, sumIntegral (𝓕:=𝓕) hW hWm T g⟫_ℝ =
      ∑ i, ⟪f i,g i⟫_ℝ := by
  classical
  simp only [sumIntegral, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · exact itoIntegralCLM_T_inner (𝓕:=𝓕) (hW i) T (hWm i) (f i) (g i)
  · intro j hj hji
    exact itoIntegral_cross_inner (hW j) (hW i) (hpair j i) (hchannels j i hji)
      (hWm j) (hWm i) T (f j) (g i)
  · simp

theorem sumIntegral_norm_sq
    (hpair : ∀ i j, PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (f : ι → Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    ‖sumIntegral (𝓕:=𝓕) hW hWm T f‖^2 = ∑ i, ‖f i‖^2 := by
  simpa only [real_inner_self_eq_norm_sq] using sumIntegral_inner hW hWm hpair hchannels T f f

end LinearStochastic.CommonItoMultichannel
