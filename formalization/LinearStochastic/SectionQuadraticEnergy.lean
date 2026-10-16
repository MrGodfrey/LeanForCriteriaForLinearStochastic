import LinearStochastic.SectionSolutionNaturality

/-! Actual quadratic energy of a genuine integral solution.  This is the
stochastic product identity applied to the true linear image by H; no energy
formula or decay estimate is supplied as a premise. -/
noncomputable section
namespace LinearStochastic.SectionQuadraticEnergy
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality SectionSolutionNaturality

variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

omit [Fintype κ] [Fintype ι] [IsProbabilityMeasure μ] [CompleteSpace E] in
/-- Symmetry is preserved on actual L² equivalence classes. -/
theorem symmetric_compLp (H : E →L[ℝ] E) (hH : H.IsSymmetric)
    {Λ : Type*} {mΛ : MeasurableSpace Λ} {ν : Measure Λ} (f g : Lp E 2 ν) :
    inner ℝ f (H.compLp g) = inner ℝ (H.compLp f) g := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [H.coeFn_compLp f, H.coeFn_compLp g] with z hf hg
  rw [hf,hg]
  exact (hH (f z) (g z)).symm

/-- The real quadratic Itô energy equality, with random F₀ initial value,
actual Lebesgue drift, actual multichannel diffusion and a separate endpoint. -/
theorem energy_identity
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (H : E →L[ℝ] E) (hH : H.IsSymmetric)
    (ξ XT : Ω → E) (hξ : MemLp ξ 2 μ) (hξ0 : StronglyMeasurable[𝓕 0] ξ)
    (f X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT) :
    (∫ ω, inner ℝ (XT ω) (H (XT ω)) ∂μ) =
      (∫ ω, inner ℝ (ξ ω) (H (ξ ω)) ∂μ) +
      (∑ i, inner ℝ (φ i) (H.compLp (φ i))) + 2 * inner ℝ f (H.compLp X) := by
  have hm := SectionIntegralSolution.map b hW hWm T H ξ f φ X XT hX
  have he := integral_solution_product b hW hWm hpair hchannels T ξ (fun ω => H (ξ ω))
    hξ (H.comp_memLp' hξ) hξ0 (H.continuous.comp_stronglyMeasurable hξ0)
    f (H.compLp f) X (H.compLp X) φ (fun i => H.compLp (φ i)) XT (fun ω => H (XT ω)) hX hm
  have hs : inner ℝ X (H.compLp f) = inner ℝ f (H.compLp X) := by
    rw [symmetric_compLp H hH X f, real_inner_comm]
  rw [hs] at he
  linarith

end LinearStochastic.SectionQuadraticEnergy
