module

public import LinearStochastic.ActualTerminalOperator

@[expose] public section

/-! The Hilbert adjoint of the genuine SDE terminal operator is the genuine
BSDE observation. This strengthens a pairing-only interface to an equality of
actual Hilbert-space elements; no abstract observation map is postulated. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.ActualAdjointIdentity
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality ActualTerminalOperator
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

local instance terminalFact (t : ℝ≥0) : Fact (𝓕 t ≤ mΩ) := ⟨𝓕.le t⟩

include c hpair hchannels in
/-- The actual adjoint equality for every genuine backward solution. The
terminal datum lives in the full original F_T L² space. -/
theorem adjoint_eq (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ζ : Ω → E) (η : lpMeas E ℝ (𝓕 T) 2 μ)
    (hζ : StronglyMeasurable[𝓕 0] ζ) (hζ2 : MemLp ζ 2 μ)
    (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hY : SectionIntegralSolution b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T ζ
      (-(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (Z i))) Z Y (η : Lp E 2 μ)) :
    (terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D).adjoint η =
      B.adjoint.compLp Y+∑ i, (D i).adjoint.compLp (Z i) := by
  letI : Fact (𝓕 T ≤ mΩ) := ⟨𝓕.le T⟩
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  obtain ⟨X,hX⟩ := terminal_spec (𝓕:=𝓕) b c hW hWm i₀ T A B C D u
  have hd := SectionLinearDuality.forward_backward_duality b
    (fun i ↦ (hW i).toIsPreBrownianReal) hWm hpair hchannels T A B C D
    (0 : Ω → E) ζ
    (terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D u : Lp E 2 μ)
    (η : Lp E 2 μ) MemLp.zero hζ2 stronglyMeasurable_zero hζ X Y u Z hX hY
  change inner ℝ (terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D u : Lp E 2 μ)
    (η : Lp E 2 μ) = _
  rw [L2.inner_def]
  simpa only [Pi.zero_apply,inner_zero_left,integral_zero,zero_add] using hd

include c hpair hchannels in
/-- Zero observation is exactly membership in the kernel of the actual
terminal-map adjoint, with the same real terminal datum. -/
theorem adjoint_zero_iff (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ζ : Ω → E) (η : lpMeas E ℝ (𝓕 T) 2 μ)
    (hζ : StronglyMeasurable[𝓕 0] ζ) (hζ2 : MemLp ζ 2 μ)
    (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hY : SectionIntegralSolution b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T ζ
      (-(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (Z i))) Z Y (η : Lp E 2 μ)) :
    (terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D).adjoint η = 0 ↔
      B.adjoint.compLp Y+∑ i, (D i).adjoint.compLp (Z i) = 0 := by
  rw [adjoint_eq b c hW hWm hpair hchannels i₀ T A B C D ζ η hζ hζ2 Y Z hY]

end LinearStochastic.ActualAdjointIdentity
