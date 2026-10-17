module

public import LinearStochastic.ProgressiveControlSection
public import LinearStochastic.HilbertBrownianRealization
public import LinearStochastic.ActualControlProperties

@[expose] public section

/-! Equivalence of the section-based predicates and ordinary progressive
finite-energy controls with genuine raw continuous S² solutions and the
paper's expected squared terminal error. -/
noncomputable section
namespace LinearStochastic.RawControlProperties
open MeasureTheory ProbabilityTheory
open scoped NNReal
open CommonItoMultichannel ProgressiveControlSection SectionLinearDuality
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)

/-- A raw solution attaining the expected squared terminal error bound. The
ordinary progressive control need not itself be predictable; u is its proved
representative and coefficient_ae identifies the actual raw integrands. -/
def Reach (v₀ : E) (η : Lp E 2 μ) (ε : ℝ) : Prop :=
  ∃ (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)),
    RawSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T (fun _ => v₀) A B C D v R u X ∧
      (∫ ω, ‖R T ω-η ω‖^2 ∂μ) < ε

/-- Ordinary-progressive, raw-solution approximate controllability. -/
def Approximate : Prop :=
  ∀ (v₀ : E) (η : Lp E 2 μ), AEStronglyMeasurable[𝓕 T] η μ →
    ∀ ε : ℝ, 0 < ε → Reach (𝓕:=𝓕) b hW hWm T A B C D v₀ η ε

/-- Ordinary-progressive, raw-solution approximate null controllability. -/
def ApproximateNull : Prop :=
  ∀ (v₀ : E) (ε : ℝ), 0 < ε → Reach (𝓕:=𝓕) b hW hWm T A B C D v₀ 0 ε

include c in
omit [CompleteSpace U] in
/-- Actual raw reachability and actual section reachability have exactly the
same terminal accuracy, in both directions. -/
theorem reach_iff (i₀ : ι) (v₀ : E) (η : Lp E 2 μ) (ε : ℝ) :
    Reach (𝓕:=𝓕) b hW hWm T A B C D v₀ η ε ↔
      ∃ u X XT, ActualControlProperties.ControlledTerminal (𝓕:=𝓕) b
        (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D v₀ u X XT ∧ ‖XT-η‖^2 < ε := by
  constructor
  · rintro ⟨v,R,u,X,q,herr⟩
    have hs := RawSolution.to_section b (fun i => (hW i).toIsPreBrownianReal) hWm T
      (fun _ => v₀) A B C D v R u X q
    have h2 := CommonProcessSpace.eval_memLp_of_s2 q.progressive.stronglyAdapted T q.continuous q.squareSup le_rfl
    let XT := h2.toLp (R T)
    have ht : XT =ᵐ[μ] R T := h2.coeFn_toLp
    have he : ‖XT-η‖^2 = ∫ ω, ‖R T ω-η ω‖^2 ∂μ := by
      rw [ActualControlProperties.norm_error_sq XT η]
      exact integral_congr_ae (ht.mono (fun ω hω => by dsimp only; rw [hω]))
    refine ⟨u,X,XT,?_,he.trans_lt herr⟩
    exact SectionSolutionLinearity.SectionIntegralSolution.terminal_congr b
      (fun i => (hW i).toIsPreBrownianReal) hWm T (fun _ => v₀) (R T) XT _ _ _ hs ht
  · rintro ⟨u,X,XT,hX,herr⟩
    obtain ⟨R,hp,hc,h2,hrep,h0,hend,heq⟩ := HilbertBrownianRealization.exists_realization b c hW hWm
      i₀ T A B C D (fun _ => v₀) stronglyMeasurable_const (memLp_const v₀) u X XT hX
    have q := RawSolution.of_class_path b (fun i => (hW i).toIsPreBrownianReal) hWm T
      (fun _ => v₀) A B C D R u X hp hc h2 hrep heq
    refine ⟨(fun t ω => u (t,ω)),R,u,X,q,?_⟩
    have he : (∫ ω, ‖R T ω-η ω‖^2 ∂μ) = ‖XT-η‖^2 := by
      rw [ActualControlProperties.norm_error_sq XT η]
      exact integral_congr_ae (hend.mono (fun ω hω => by dsimp only; rw [hω]))
    exact he.trans_lt herr

include c in
omit [CompleteSpace U] in
/-- The ordinary progressive formulation and the proved section formulation
of AC coincide; neither direction restricts the allowable raw controls. -/
theorem approximate_iff (i₀ : ι) :
    Approximate (𝓕:=𝓕) b hW hWm T A B C D ↔
      ActualControlProperties.Approximate (𝓕:=𝓕) b (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D := by
  constructor
  · intro h v η hη ε hε
    exact (reach_iff b c hW hWm T A B C D i₀ v η ε).mp (h v η hη ε hε)
  · intro h v η hη ε hε
    exact (reach_iff b c hW hWm T A B C D i₀ v η ε).mpr (h v η hη ε hε)

include c in
omit [CompleteSpace U] in
/-- In particular ANC is not narrowed to a smaller class of controls: every
ordinary progressive raw solution is admitted by the reverse implication. -/
theorem approximateNull_iff (i₀ : ι) :
    ApproximateNull (𝓕:=𝓕) b hW hWm T A B C D ↔
      ActualControlProperties.ApproximateNull (𝓕:=𝓕) b (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D := by
  constructor
  · intro h v ε hε
    simpa only [sub_zero] using (reach_iff b c hW hWm T A B C D i₀ v 0 ε).mp (h v ε hε)
  · intro h v ε hε
    apply (reach_iff b c hW hWm T A B C D i₀ v 0 ε).mpr
    simpa only [sub_zero] using h v ε hε

omit hW hWm b c [Fintype κ] [Fintype τ] [Fintype ι] [CompleteSpace E] [CompleteSpace U] [𝓕.IsComplete μ] [IsProbabilityMeasure μ] [InnerProductSpace ℝ E] in
/-- The null-target error is precisely the paper's expected squared state norm. -/
theorem null_error (R : ℝ≥0 → Ω → E) :
    (∫ ω, ‖R T ω-(0 : Lp E 2 μ) ω‖^2 ∂μ) = ∫ ω, ‖R T ω‖^2 ∂μ := by
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_zero E 2 μ] with ω hω
  simp only [hω,Pi.zero_apply,sub_zero]

end LinearStochastic.RawControlProperties
