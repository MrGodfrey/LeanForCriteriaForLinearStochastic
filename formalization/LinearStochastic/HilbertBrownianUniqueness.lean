module

public import LinearStochastic.HilbertBrownianRealization

@[expose] public section

/-! Genuine arbitrary-horizon uniqueness of section-based terminal states,
proved by reconstructing continuous S² solutions and applying actual global
pathwise uniqueness, not by assuming a terminal-map property. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.HilbertBrownianUniqueness
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality HilbertLocalSolution HilbertBrownianRealization
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

include c in
/-- Any two original Hilbert integral solutions with the same control and
initial value have the same actual terminal value at every finite horizon. -/
theorem terminal_unique (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    (X Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT YT : Ω → E)
    (hX : SectionIntegralSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ (A.compLp X+B.compLp u)
      (fun i => (C i).compLp X+(D i).compLp u) X XT)
    (hY : SectionIntegralSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ (A.compLp Y+B.compLp u)
      (fun i => (C i).compLp Y+(D i).compLp u) Y YT) : XT =ᵐ[μ] YT := by
  let q := coordinateSolution b c hW hWm i₀ T A B C D ξ hξ hξ2 u X XT hX
  let r := coordinateSolution b c hW hWm i₀ T A B C D ξ hξ hξ2 u Y YT hY
  have hp := CommonBrownianGlobal.global_unique hW hWm i₀ T
    (coefficientMatrix b b A) (coefficientMatrix b c B)
    (fun i => coefficientMatrix b b (C i)) (fun i => coefficientMatrix b c (D i))
    (fun j ω => inner ℝ (b j) (ξ ω))
    (fun j => (innerSL ℝ (b j)).continuous.comp_stronglyMeasurable hξ)
    (fun j => (innerSL ℝ (b j)).comp_memLp' hξ2)
    (fun j => VectorItoProduct.coordinate c j u) q r
  have hx : ∀ᵐ ω ∂μ, ∀ j, inner ℝ (b j) (XT ω) = q.path j T ω := by
    rw [ae_all_iff]
    exact coordinateSolution_terminal b c hW hWm i₀ T A B C D ξ hξ hξ2 u X XT hX
  have hy : ∀ᵐ ω ∂μ, ∀ j, inner ℝ (b j) (YT ω) = r.path j T ω := by
    rw [ae_all_iff]
    exact coordinateSolution_terminal b c hW hWm i₀ T A B C D ξ hξ hξ2 u Y YT hY
  filter_upwards [hp,hx,hy] with ω hp hx hy
  calc
    XT ω = ∑ j, inner ℝ (b j) (XT ω) • b j := (b.sum_repr' _).symm
    _ = ∑ j, inner ℝ (b j) (YT ω) • b j := Finset.sum_congr rfl (fun j _ => by rw [hx j,hy j,hp j T le_rfl])
    _ = YT ω := b.sum_repr' _

end LinearStochastic.HilbertBrownianUniqueness
