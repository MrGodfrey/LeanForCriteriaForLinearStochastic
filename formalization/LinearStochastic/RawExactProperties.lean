import LinearStochastic.RawControlProperties
import LinearStochastic.ExactTerminalProperties

/-! Exact controllability predicates in the ordinary progressive-control and
raw continuous-S² path formulation are equivalent to the actual section
predicates. Endpoint equality is almost-sure equality, never a time-a.e. claim. -/
noncomputable section
namespace LinearStochastic.RawExactProperties
open MeasureTheory ProbabilityTheory
open scoped NNReal
open CommonItoMultichannel ProgressiveControlSection
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)

/-- Exact attainment by an ordinary progressive finite-energy control and
an actual original raw continuous S² solution. -/
def Reach (v₀ : E) (η : Lp E 2 μ) : Prop :=
  ∃ (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)),
    RawSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T (fun _ => v₀) A B C D v R u X ∧
      R T =ᵐ[μ] η

def Exact : Prop :=
  ∀ (v₀ : E) (η : Lp E 2 μ), AEStronglyMeasurable[𝓕 T] η μ → Reach (𝓕:=𝓕) b hW hWm T A B C D v₀ η

def ExactNull : Prop := ∀ v₀ : E, Reach (𝓕:=𝓕) b hW hWm T A B C D v₀ 0

def ExactTerminal : Prop :=
  ∀ η : Lp E 2 μ, AEStronglyMeasurable[𝓕 T] η μ → ∃ v₀ : E, Reach (𝓕:=𝓕) b hW hWm T A B C D v₀ η

include c in
/-- Actual raw endpoint attainment and actual section endpoint attainment
coincide, for exactly the same deterministic initial state and L² target. -/
theorem reach_iff (i₀ : ι) (v₀ : E) (η : Lp E 2 μ) :
    Reach (𝓕:=𝓕) b hW hWm T A B C D v₀ η ↔
      ∃ u X, ActualControlProperties.ControlledTerminal (𝓕:=𝓕) b
        (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D v₀ u X η := by
  constructor
  · rintro ⟨v,R,u,X,q,hend⟩
    have hs := RawSolution.to_section b (fun i => (hW i).toIsPreBrownianReal) hWm T
      (fun _ => v₀) A B C D v R u X q
    exact ⟨u,X,SectionSolutionLinearity.SectionIntegralSolution.terminal_congr b
      (fun i => (hW i).toIsPreBrownianReal) hWm T (fun _ => v₀) (R T) η _ _ _ hs hend.symm⟩
  · rintro ⟨u,X,hX⟩
    obtain ⟨R,hp,hc,h2,hrep,_,hend,heq⟩ := HilbertBrownianRealization.exists_realization b c hW hWm
      i₀ T A B C D (fun _ => v₀) stronglyMeasurable_const (memLp_const v₀) u X η hX
    exact ⟨(fun t ω => u (t,ω)),R,u,X,
      RawSolution.of_class_path b (fun i => (hW i).toIsPreBrownianReal) hWm T
        (fun _ => v₀) A B C D R u X hp hc h2 hrep heq,hend⟩

include c in
theorem exact_iff (i₀ : ι) : Exact (𝓕:=𝓕) b hW hWm T A B C D ↔
    ActualControlProperties.Exact (𝓕:=𝓕) b (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D := by
  constructor
  · intro h v η hη
    exact (reach_iff b c hW hWm T A B C D i₀ v η).mp (h v η hη)
  · intro h v η hη
    exact (reach_iff b c hW hWm T A B C D i₀ v η).mpr (h v η hη)

include c in
theorem exactNull_iff (i₀ : ι) : ExactNull (𝓕:=𝓕) b hW hWm T A B C D ↔
    ActualControlProperties.ExactNull (𝓕:=𝓕) b (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D := by
  constructor
  · intro h v
    exact (reach_iff b c hW hWm T A B C D i₀ v 0).mp (h v)
  · intro h v
    exact (reach_iff b c hW hWm T A B C D i₀ v 0).mpr (h v)

include c in
theorem exactTerminal_iff (i₀ : ι) : ExactTerminal (𝓕:=𝓕) b hW hWm T A B C D ↔
    ExactTerminalProperties.ExactTerminal (𝓕:=𝓕) b (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D := by
  constructor
  · intro h η hη
    obtain ⟨v,hv⟩ := h η hη
    exact ⟨v,(reach_iff b c hW hWm T A B C D i₀ v η).mp hv⟩
  · intro h η hη
    obtain ⟨v,hv⟩ := h η hη
    exact ⟨v,(reach_iff b c hW hWm T A B C D i₀ v η).mpr hv⟩

include c in
/-- The paper's exact-terminal interpretation also holds with ordinary
progressive controls and actual raw continuous S² trajectories. -/
theorem exact_iff_terminal_and_null (i₀ : ι) :
    Exact (𝓕:=𝓕) b hW hWm T A B C D ↔
      ExactTerminal (𝓕:=𝓕) b hW hWm T A B C D ∧ ExactNull (𝓕:=𝓕) b hW hWm T A B C D := by
  rw [exact_iff b c hW hWm T A B C D i₀,exactTerminal_iff b c hW hWm T A B C D i₀,
    exactNull_iff b c hW hWm T A B C D i₀]
  exact ExactTerminalProperties.exact_iff_terminal_and_null b (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D

end LinearStochastic.RawExactProperties
