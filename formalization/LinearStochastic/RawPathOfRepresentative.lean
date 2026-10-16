import LinearStochastic.ProgressiveControlSection

/-! A raw progressive representative of the very same control gives the raw
integral equation with its literal drift and identified Itô coefficients. -/
noncomputable section
namespace LinearStochastic.RawPathOfRepresentative
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace
open CommonItoMultichannel LinearDuality SectionLinearDuality ProgressiveControlSection
variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

theorem raw_solution (T : ℝ≥0) (ξ : Ω → E)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hv : IsStronglyProgressive 𝓕 v)
    (hu : (u : ℝ≥0 × Ω → U) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry v)
    (hp : IsStronglyProgressive 𝓕 R) (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (h2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ)
    (hX : (X : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R)
    (he : ∀ t, t ≤ T → R t =ᵐ[μ] integralState b hW hWm T ξ (A.compLp X+B.compLp u)
      (fun i => (C i).compLp X+(D i).compLp u) (t:ℝ)) :
    RawSolution b hW hWm T ξ A B C D v R u X := by
  refine ⟨hv,(memLp_congr_ae hu).mp (memLp_of_memLp_trim 𝓕.predictable_le_prod (Lp.memLp u)),
    hp,hc,h2,hu,hX,?_⟩
  intro t ht
  filter_upwards [he t ht,primitive_ae T t (by exact_mod_cast ht) A B v R u X hu hX] with ω he hd
  simpa only [integralState,Real.toNNReal_coe,hd] using he

end LinearStochastic.RawPathOfRepresentative
