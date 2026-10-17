module

public import LinearStochastic.HilbertSwitchingUniqueness
public import LinearStochastic.ProgressiveControlSection

@[expose] public section

/-! Ordinary progressive raw S² solutions of the literal singular feedback
have a unique state path and control class. No equality of controls is presumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.RawSwitchingUniqueness
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace
open CommonItoMultichannel ProgressiveControlSection
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (i₀ : ι) (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
  (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)

omit [CompleteSpace U] in
include c i₀ hξ hξ2 in
/-- True uniqueness of the closed-loop equation with a possibly singular
piecewise gain: two arbitrary raw progressive S² solutions have the same path
on a single full-probability event and the same actual predictable control. -/
theorem unique (hT : 0 < T) (K : ℕ → E →L[ℝ] U) (R S : ℝ≥0 → Ω → E)
    (u v : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X Y : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (q : RawSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ A B C D
      (SwitchingFeedbackIdentity.feedback T K R) R u X)
    (r : RawSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ A B C D
      (SwitchingFeedbackIdentity.feedback T K S) S v Y) :
    X = Y ∧ u = v ∧ ∀ᵐ ω ∂μ, ∀ t, t ≤ T → R t ω = S t ω :=
  HilbertSwitchingUniqueness.unique b c hW hWm i₀ T A B C D ξ hξ hξ2 u v X Y (R T) (S T)
    (q.to_section b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ A B C D _ R u X)
    (r.to_section b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ A B C D _ S v Y)
    hT K R S q.state_rep r.state_rep q.continuous r.continuous q.control_rep r.control_rep

end LinearStochastic.RawSwitchingUniqueness
