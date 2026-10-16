import LinearStochastic.SectionLinearDuality

/-! A genuine zero-observation backward solution with nonzero deterministic
initial value separates every actual forward terminal state from zero by a
strict positive L² distance. This is derived from actual stochastic duality. -/
noncomputable section
namespace LinearStochastic.ZeroObservationSeparation
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel LinearDuality SectionLinearDuality

section L2
variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem integral_inner_le_norm (X Y : Ω → E) (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    (∫ ω, inner ℝ (X ω) (Y ω) ∂μ) ≤ ‖hX.toLp X‖ * ‖hY.toLp Y‖ := by
  have he : (∫ ω, inner ℝ (X ω) (Y ω) ∂μ) = inner ℝ (hX.toLp X) (hY.toLp Y) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hX.coeFn_toLp,hY.coeFn_toLp] with ω hx hy
    rw [hx,hy]
  rw [he]
  exact real_inner_le_norm _ _
end L2

section Solutions
variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Exact nonzero terminal pairing for every actual controlled forward
solution starting from the same deterministic obstruction vector. -/
theorem terminal_pairing
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (v : E) (XT YT : Ω → E)
    (X Y : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T (fun _ => v) (A.compLp X + B.compLp u)
      (fun i => (C i).compLp X + (D i).compLp u) X XT)
    (hY : SectionIntegralSolution b hW hWm T (fun _ => v)
      (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y YT)
    (hobs : B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i) = 0) :
    (∫ ω, inner ℝ (XT ω) (YT ω) ∂μ) = ‖v‖ ^ 2 := by
  have h := SectionLinearDuality.forward_backward_duality b hW hWm hpair hchannels T A B C D
    (fun _ => v) (fun _ => v) XT YT (memLp_const v) (memLp_const v)
    stronglyMeasurable_const stronglyMeasurable_const X Y u Z hX hY
  simpa [hobs,real_inner_self_eq_norm_sq] using h

/-- A single positive distance excludes approximate null controllability for
the full family of actual forward solutions. No terminal operator or abstract
duality property is supplied in place of the SDE equations. -/
theorem positive_terminal_distance
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (v : E) (hv : v ≠ 0) (YT : Ω → E) (hYT : MemLp YT 2 μ)
    (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hY : SectionIntegralSolution b hW hWm T (fun _ => v)
      (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y YT)
    (hobs : B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i) = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (u : Lp U 2 (spacetimeMeasure 𝓕 μ T))
      (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Ω → E) (hXT : MemLp XT 2 μ),
      SectionIntegralSolution b hW hWm T (fun _ => v) (A.compLp X + B.compLp u)
        (fun i => (C i).compLp X + (D i).compLp u) X XT → ε ≤ ‖hXT.toLp XT‖ := by
  let ε := ‖v‖ ^ 2 / (‖hYT.toLp YT‖ + 1)
  have hp : 0 < ‖hYT.toLp YT‖ + 1 := by positivity
  refine ⟨ε,div_pos (sq_pos_of_pos (norm_pos_iff.mpr hv)) hp,?_⟩
  intro u X XT hXT hX
  have h := integral_inner_le_norm XT YT hXT hYT
  rw [terminal_pairing b hW hWm hpair hchannels T A B C D v XT YT X Y u Z hX hY hobs] at h
  apply (div_le_iff₀ hp).mpr
  nlinarith [norm_nonneg (hXT.toLp XT)]
end Solutions

#print axioms positive_terminal_distance
end LinearStochastic.ZeroObservationSeparation
