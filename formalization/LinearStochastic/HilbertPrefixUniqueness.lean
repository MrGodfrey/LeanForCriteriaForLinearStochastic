import LinearStochastic.HilbertSectionPrefix
import LinearStochastic.HilbertBrownianUniqueness

/-! Two actual controlled solutions with equal controls on a prefix have the
same actual endpoint of that prefix, irrespective of later controls. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.HilbertPrefixUniqueness
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
open CommonItoMultichannel SectionLinearDuality LinearDuality VectorHorizonRestriction
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι]
  (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

include c in
theorem at_prefix (i₀ : ι) {t T : ℝ≥0} (h : t ≤ T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (u v : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    (X Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT YT Xt Yt : Ω → E)
    (hX : SectionIntegralSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
      (A.compLp X+B.compLp u) (fun i => (C i).compLp X+(D i).compLp u) X XT)
    (hY : SectionIntegralSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
      (A.compLp Y+B.compLp v) (fun i => (C i).compLp Y+(D i).compLp v) Y YT)
    (hx : Xt =ᵐ[μ] integralState b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
      (A.compLp X+B.compLp u) (fun i => (C i).compLp X+(D i).compLp u) (t:ℝ))
    (hy : Yt =ᵐ[μ] integralState b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
      (A.compLp Y+B.compLp v) (fun i => (C i).compLp Y+(D i).compLp v) (t:ℝ))
    (huv : restrict h u = restrict h v) : Xt =ᵐ[μ] Yt := by
  have hp := HilbertSectionPrefix.controlled_prefix b (fun i => (hW i).toIsPreBrownianReal) hWm
    h A B C D ξ XT Xt u X hX hx
  have hq := HilbertSectionPrefix.controlled_prefix b (fun i => (hW i).toIsPreBrownianReal) hWm
    h A B C D ξ YT Yt v Y hY hy
  rw [huv] at hp
  exact HilbertBrownianUniqueness.terminal_unique b c hW hWm i₀ t A B C D ξ hξ hξ2
    (restrict h v) (restrict h X) (restrict h Y) Xt Yt hp hq

end LinearStochastic.HilbertPrefixUniqueness
