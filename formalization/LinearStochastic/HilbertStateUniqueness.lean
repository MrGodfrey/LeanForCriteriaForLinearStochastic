import LinearStochastic.HilbertBrownianRealization

/-! Uniqueness of the whole genuine Hilbert state class, not merely of its
terminal value, under the original Brownian assumptions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.HilbertStateUniqueness
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality HilbertLocalSolution
open HilbertBrownianRealization LpOrthonormalCoordinates VectorItoProduct
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

include c in
/-- Any two actual section solutions have the same full state class; the
conclusion follows from true coordinate pathwise uniqueness and measurable
product comparison, not from endpoint equality. -/
theorem state_unique (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    (X Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT YT : Ω → E)
    (hX : SectionIntegralSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
      (A.compLp X+B.compLp u) (fun i => (C i).compLp X+(D i).compLp u) X XT)
    (hY : SectionIntegralSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
      (A.compLp Y+B.compLp u) (fun i => (C i).compLp Y+(D i).compLp u) Y YT) : X=Y := by
  let q := coordinateSolution b c hW hWm i₀ T A B C D ξ hξ hξ2 u X XT hX
  let r := coordinateSolution b c hW hWm i₀ T A B C D ξ hξ hξ2 u Y YT hY
  have hp := CommonBrownianGlobal.global_unique hW hWm i₀ T
    (coefficientMatrix b b A) (coefficientMatrix b c B)
    (fun i => coefficientMatrix b b (C i)) (fun i => coefficientMatrix b c (D i))
    (fun j ω => inner ℝ (b j) (ξ ω))
    (fun j => (innerSL ℝ (b j)).continuous.comp_stronglyMeasurable hξ)
    (fun j => (innerSL ℝ (b j)).comp_memLp' hξ2)
    (fun j => coordinate c j u) q r
  have heq : (fun j => coordinate b j X) = fun j => coordinate b j Y := by
    funext j
    have hm := CommonProgressiveComparison.product_ae_of_modification T (q.progressive j)
      (r.progressive j) (fun s hs => hp.mono (fun ω hω => hω j s hs))
    apply Lp.ext
    apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
      𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
    exact (q.representative j).trans (hm.trans (r.representative j).symm)
  exact (assemble_coordinates (mΛ:=𝓕.predictable) b X).symm.trans
    ((congrArg (assemble (mΛ:=𝓕.predictable) b) heq).trans
      (assemble_coordinates (mΛ:=𝓕.predictable) b Y))
end LinearStochastic.HilbertStateUniqueness
