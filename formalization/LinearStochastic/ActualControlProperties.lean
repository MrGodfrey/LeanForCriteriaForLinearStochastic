module

public import LinearStochastic.GlobalInvariantObstruction
public import LinearStochastic.ActualApproximation

@[expose] public section

/-! Controllability properties stated with the original controlled integral
 equation, rather than an abstract terminal map. These definitions quantify
 SectionIntegralSolution; identifying every such L² solution with the unique
 continuous S² realization is a separate analytic bridge. -/
noncomputable section
namespace LinearStochastic.ActualControlProperties
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality

variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)

/-- Actual original equation from a deterministic initial state, with an L²
terminal variable and a predictable L² control. -/
def ControlledTerminal (v : E) (u : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Lp E 2 μ) : Prop :=
  SectionIntegralSolution b hW hWm T (fun _ => v) (A.compLp X+B.compLp u)
    (fun i => (C i).compLp X+(D i).compLp u) X XT

/-- Approximate controllability with all original F_T-measurable L² targets. -/
def Approximate : Prop :=
  ∀ (v : E) (η : Lp E 2 μ), AEStronglyMeasurable[𝓕 T] η μ → ∀ ε : ℝ, 0 < ε →
    ∃ u X XT, ControlledTerminal (𝓕:=𝓕) b hW hWm T A B C D v u X XT ∧ ‖XT-η‖^2 < ε

/-- Approximate null controllability for every deterministic initial state. -/
def ApproximateNull : Prop :=
  ∀ (v : E) (ε : ℝ), 0 < ε →
    ∃ u X XT, ControlledTerminal (𝓕:=𝓕) b hW hWm T A B C D v u X XT ∧ ‖XT‖^2 < ε

/-- Exact controllability; equality in L² is almost-sure terminal equality. -/
def Exact : Prop :=
  ∀ (v : E) (η : Lp E 2 μ), AEStronglyMeasurable[𝓕 T] η μ →
    ∃ u X, ControlledTerminal (𝓕:=𝓕) b hW hWm T A B C D v u X η

/-- Exact null controllability by a genuine predictable finite-energy control. -/
def ExactNull : Prop :=
  ∀ v : E, ∃ u X, ControlledTerminal (𝓕:=𝓕) b hW hWm T A B C D v u X 0

omit [IsProbabilityMeasure μ] [CompleteSpace E] in
/-- The L² squared error in the definitions is exactly the expected squared
Euclidean error, with arbitrary Hilbert-valued terminal random variables. -/
theorem norm_error_sq (XT η : Lp E 2 μ) :
    ‖XT-η‖^2 = ∫ ω, ‖XT ω-η ω‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub XT η] with ω hω
  rw [hω,real_inner_self_eq_norm_sq]
  rfl

omit [CompleteSpace E] [CompleteSpace U] in
theorem exact_implies_approximate (h : Exact (𝓕:=𝓕) b hW hWm T A B C D) :
    Approximate (𝓕:=𝓕) b hW hWm T A B C D := by
  intro v η hη ε hε
  obtain ⟨u,X,hX⟩ := h v η hη
  exact ⟨u,X,η,hX,by simpa using hε⟩

omit [CompleteSpace E] [CompleteSpace U] in
theorem exact_implies_exactNull (h : Exact (𝓕:=𝓕) b hW hWm T A B C D) :
    ExactNull (𝓕:=𝓕) b hW hWm T A B C D := by
  intro v
  exact h v 0 (aestronglyMeasurable_zero.congr (Lp.coeFn_zero E 2 μ).symm)

omit [CompleteSpace E] [CompleteSpace U] in
theorem exactNull_implies_approximateNull (h : ExactNull (𝓕:=𝓕) b hW hWm T A B C D) :
    ApproximateNull (𝓕:=𝓕) b hW hWm T A B C D := by
  intro v ε hε
  obtain ⟨u,X,hX⟩ := h v
  exact ⟨u,X,0,hX,by simpa using hε⟩

omit [CompleteSpace E] [CompleteSpace U] in
theorem approximate_implies_approximateNull (h : Approximate (𝓕:=𝓕) b hW hWm T A B C D) :
    ApproximateNull (𝓕:=𝓕) b hW hWm T A B C D := by
  intro v ε hε
  simpa using h v 0 (aestronglyMeasurable_zero.congr (Lp.coeFn_zero E 2 μ).symm) ε hε

/-- At every prescribed horizon, actual approximate null controllability
forces the actual terminal obstruction flag to vanish. The separating
zero-observation adjoint is constructed by the proved global SDE theorem. -/
theorem flag_zero_of_approximateNull [FiniteDimensional ℝ E] [𝓕.IsComplete μ]
    (hWc : ∀ i ω, Continuous fun t => W i t ω) (i₀ : ι)
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t => W i t ω) (fun ω t => W j t ω) μ)
    (h : ApproximateNull (𝓕:=𝓕) b hW hWm T A B C D) :
    (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥ := by
  by_contra hflag
  obtain ⟨v,_,ε,hε,hsep⟩ := GlobalInvariantObstruction.positive_horizon_separation
    b hW hWm hWc i₀ T hpair hchannels A B C D hflag
  obtain ⟨u,X,XT,hX,hsmall⟩ := h v (ε^2) (sq_pos_of_pos hε)
  have hlarge := hsep u X XT (Lp.memLp XT) hX
  rw [Lp.toLp_coeFn] at hlarge
  nlinarith [norm_nonneg XT]

omit [CompleteSpace U] in
/-- Density of the actual zero-initial reachable subspace gives the actual
approximation property for deterministic initial states. -/
theorem approximate_of_dense [𝓕.IsComplete μ] {τ : Type*} [Fintype τ]
    (c : OrthonormalBasis τ ℝ U) (hWc : ∀ i ω, Continuous fun t => W i t ω) (i₀ : ι)
    (hd : Dense (ActualReachableDensity.relativeTerminals (𝓕:=𝓕) b hW hWm T A B C D :
      Set (lpMeas E ℝ (𝓕 T) 2 μ))) : Approximate (𝓕:=𝓕) b hW hWm T A B C D := by
  intro v η hη ε hε
  exact ActualApproximation.approximation_from_initial b c hW hWm hWc i₀ T A B C D hd
    (fun _ => v) stronglyMeasurable_const (memLp_const v) η hη ε hε

end LinearStochastic.ActualControlProperties
