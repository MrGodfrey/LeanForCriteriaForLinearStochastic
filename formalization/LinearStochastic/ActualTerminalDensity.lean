import LinearStochastic.ActualTerminalOperator
import LinearStochastic.RawControlProperties
import LinearStochastic.ControlDriverTransport
import LinearStochastic.HilbertDuality

/-! The manuscript's density criterion for the actual SDE terminal operator,
with original Brownian drivers and ordinary progressive raw controls. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace LinearStochastic.ActualTerminalDensity
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
open CommonItoMultichannel SectionLinearDuality ActualTerminalOperator
open ActualReachableDensity CommonBrownianRepair
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (i₀ : ι) (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)

local instance terminalFact (t : ℝ≥0) : Fact (𝓕 t ≤ mΩ) := ⟨𝓕.le t⟩

omit [CompleteSpace U] in
/-- The actual operator range equals the actual reachable subspace, not its span. -/
theorem range_eq :
    (terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D).range =
      relativeTerminals (𝓕:=𝓕) b (fun i=>(hW i).toIsPreBrownianReal) hWm T A B C D := by
  ext η
  constructor
  · rintro ⟨u,rfl⟩
    obtain ⟨X,hX⟩ := terminal_spec (𝓕:=𝓕) b c hW hWm i₀ T A B C D u
    exact ⟨u,X,hX⟩
  · rintro ⟨u,X,hX⟩
    refine ⟨u,Subtype.ext ?_⟩
    exact terminal_eq (𝓕:=𝓕) b c hW hWm i₀ T A B C D u X η hX

omit [CompleteSpace U] in
/-- Driver repair preserves the actual reachable set on the same filtration. -/
theorem repaired_relative_eq :
    relativeTerminals (𝓕:=𝓕) b (fun i=>(repaired_brownian hW i).toIsPreBrownianReal)
      (repaired_measurable hW) T A B C D =
    relativeTerminals (𝓕:=𝓕) b (fun i=>(hW i).toIsPreBrownianReal) hWm T A B C D := by
  ext η
  constructor
  · rintro ⟨u,X,hX⟩
    exact ⟨u,X,SectionDriverTransport.solution b
      (fun i=>(repaired_brownian hW i).toIsPreBrownianReal) (fun i=>(hW i).toIsPreBrownianReal)
      (repaired_measurable hW) hWm (fun i=>(hW i).mk_ae_forall_eq) T _ _ _ _ _ hX⟩
  · rintro ⟨u,X,hX⟩
    exact ⟨u,X,SectionDriverTransport.solution b
      (fun i=>(hW i).toIsPreBrownianReal) (fun i=>(repaired_brownian hW i).toIsPreBrownianReal)
      hWm (repaired_measurable hW)
      (fun i=>((hW i).mk_ae_forall_eq).mono (fun _ hω t=>(hω t).symm)) T _ _ _ _ _ hX⟩

/-- Actual AC is equivalent to density of the actual terminal operator range. -/
theorem approximate_iff_dense :
    ActualControlProperties.Approximate (𝓕:=𝓕) b (fun i=>(hW i).toIsPreBrownianReal) hWm T A B C D ↔
      Dense (Set.range (terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D)) := by
  constructor
  · intro h η
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨u,X,XT,hX,he⟩ := h 0 η (lpMeas.aestronglyMeasurable η) (ε^2) (sq_pos_of_pos hε)
    refine ⟨terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D u,⟨u,rfl⟩,?_⟩
    have ht := terminal_eq (𝓕:=𝓕) b c hW hWm i₀ T A B C D u X XT hX
    rw [dist_comm,dist_eq_norm]
    change ‖(terminal (𝓕:=𝓕) b c hW hWm i₀ T A B C D u : Lp E 2 μ)-(η:Lp E 2 μ)‖<ε
    rw [ht]
    nlinarith [norm_nonneg (XT-(η:Lp E 2 μ))]
  · intro hd
    have hd' : Dense (relativeTerminals (𝓕:=𝓕) b (fun i=>(hW i).toIsPreBrownianReal) hWm T A B C D :
        Set (lpMeas E ℝ (𝓕 T) 2 μ)) := by
      rw [←range_eq b c hW hWm i₀ T A B C D]
      exact hd
    rw [←repaired_relative_eq b hW hWm T A B C D] at hd'
    have ha := ActualControlProperties.approximate_of_dense b
      (fun i=>(repaired_brownian hW i).toIsPreBrownianReal) (repaired_measurable hW)
      T A B C D c (repaired_continuous hW) i₀ hd'
    exact (ControlDriverTransport.approximate_iff b
      (fun i=>(repaired_brownian hW i).toIsPreBrownianReal) (fun i=>(hW i).toIsPreBrownianReal)
      (repaired_measurable hW) hWm (fun i=>(hW i).mk_ae_forall_eq) T A B C D).mp ha

/-- The precise actual-operator Hilbert criterion, with no assumed duality map. -/
theorem approximate_iff_adjoint_ker :
    ActualControlProperties.Approximate (𝓕:=𝓕) b (fun i=>(hW i).toIsPreBrownianReal) hWm T A B C D ↔
      (terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D).adjoint.ker = ⊥ := by
  rw [approximate_iff_dense b c hW hWm i₀ T A B C D]
  exact Submodule.dense_iff_topologicalClosure_eq_top.trans
    (HilbertDuality.dense_range_iff_adjoint_ker_eq_bot _)

/-- Ordinary progressive controls and the actual raw S² equation have the same criterion. -/
theorem raw_approximate_iff_adjoint_ker :
    RawControlProperties.Approximate (𝓕:=𝓕) b hW hWm T A B C D ↔
      (terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D).adjoint.ker = ⊥ :=
  (RawControlProperties.approximate_iff b c hW hWm T A B C D i₀).trans
    (approximate_iff_adjoint_ker b c hW hWm i₀ T A B C D)
end LinearStochastic.ActualTerminalDensity
