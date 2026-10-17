module

public import LinearStochastic.SectionQuadraticEnergy
public import LinearStochastic.LpLyapunovEstimate

@[expose] public section

/-! The actual closed-loop energy inequality, obtained by composing the
proved quadratic Itô identity and the deterministic Lyapunov inequality. -/
noncomputable section
namespace LinearStochastic.SectionLyapunovEnergy
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality
variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Every genuine solution of the homogeneous closed loop satisfies its
integrated Lyapunov energy inequality, including arbitrary F₀ L² initial data. -/
theorem energy_le
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (H A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (ρ : ℝ)
    (hH : H.IsSymmetric)
    (hq : ∀ x, (∑ i, inner ℝ (C i x) (H (C i x))) +
      2 * inner ℝ (A x) (H x) ≤ -ρ * inner ℝ x (H x))
    (ξ XT : Ω → E) (hξ : MemLp ξ 2 μ) (hξ0 : StronglyMeasurable[𝓕 0] ξ)
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ (A.compLp X)
      (fun i => (C i).compLp X) X XT) :
    (∫ ω, inner ℝ (XT ω) (H (XT ω)) ∂μ) + ρ * inner ℝ X (H.compLp X) ≤
      ∫ ω, inner ℝ (ξ ω) (H (ξ ω)) ∂μ := by
  have he := SectionQuadraticEnergy.energy_identity b hW hWm hpair hchannels T H hH
    ξ XT hξ hξ0 (A.compLp X) X (fun i => (C i).compLp X) hX
  have hl := LpLyapunovEstimate.integrated H A C ρ hq X
  linarith

end LinearStochastic.SectionLyapunovEnergy
