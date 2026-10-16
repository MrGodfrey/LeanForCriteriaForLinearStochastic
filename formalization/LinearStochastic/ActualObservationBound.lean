import LinearStochastic.ActualTerminalOperator

/-! Exact controllability of the genuine SDE implies an observability bound
for every genuine adjoint integral solution, by the actual bounded terminal
operator, open mapping, and the proved stochastic duality identity. -/
noncomputable section
namespace LinearStochastic.ActualObservationBound
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

include c hpair hchannels in
/-- No abstract duality or bounded-preimage premise is present. The input is
exact controllability as genuine integral solutions of the original equation. -/
theorem bound_of_exact (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hEC : ActualControlProperties.Exact (𝓕:=𝓕) b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A B C D) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ζ : Ω → E) (η : Lp E 2 μ)
      (_hζ : StronglyMeasurable[𝓕 0] ζ) (_hζ2 : MemLp ζ 2 μ)
      (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)),
      SectionIntegralSolution b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T ζ
        (-(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (Z i))) Z Y η →
      ‖η‖ ≤ K*‖B.adjoint.compLp Y+∑ i, (D i).adjoint.compLp (Z i)‖ := by
  letI : Fact (𝓕 T ≤ mΩ) := ⟨𝓕.le T⟩
  let M := terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D
  obtain ⟨K,hK,hbound⟩ := TerminalObservationBound.observation_bound M
    (surjective_of_exact (𝓕:=𝓕) b c hW hWm i₀ T A B C D hEC)
  refine ⟨K,hK,?_⟩
  intro ζ η hζ hζ2 Y Z hY
  have hm := SectionTerminalSpace.SectionIntegralSolution.terminal_aestronglyMeasurable b
    (fun i ↦ (hW i).toIsPreBrownianReal) hWm T ζ η _ Y Z hY hζ
  let η' : lpMeas E ℝ (𝓕 T) 2 μ := ⟨η,hm⟩
  apply hbound η' (B.adjoint.compLp Y+∑ i, (D i).adjoint.compLp (Z i))
  intro u
  obtain ⟨X,hX⟩ := terminal_spec (𝓕:=𝓕) b c hW hWm i₀ T A B C D u
  have hd := SectionLinearDuality.forward_backward_duality b
    (fun i ↦ (hW i).toIsPreBrownianReal) hWm hpair hchannels T A B C D
    (0 : Ω → E) ζ (M u : Lp E 2 μ) η MemLp.zero hζ2 stronglyMeasurable_zero hζ X Y u Z hX hY
  change inner ℝ (M u : Lp E 2 μ) η = _
  rw [L2.inner_def]
  simpa only [Pi.zero_apply,inner_zero_left,integral_zero,zero_add] using hd

end LinearStochastic.ActualObservationBound
