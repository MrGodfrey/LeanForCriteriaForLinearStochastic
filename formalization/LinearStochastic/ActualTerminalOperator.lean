import LinearStochastic.HilbertEndpointBound
import LinearStochastic.SectionDriverTransport
import LinearStochastic.HilbertGlobalSolution
import LinearStochastic.ActualControlProperties
import LinearStochastic.TerminalObservationBound

/-! The bounded terminal control operator is constructed from the actual
original Brownian SDE. Its domain and target are the genuine predictable H²
control space and F_T L² space; existence, uniqueness, linearity and boundedness
are each proved from the equation. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.ActualTerminalOperator
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality SectionSolutionLinearity
open CommonBrownianRepair
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (i₀ : ι) (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)

include c i₀ in
/-- Every actual input has a genuine terminal in the original F_T L² space. -/
theorem exists_terminal (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) :
    ∃ η : lpMeas E ℝ (𝓕 T) 2 μ, ∃ X : Lp E 2 (spacetimeMeasure 𝓕 μ T),
      SectionIntegralSolution b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T (0 : Ω → E)
        (A.compLp X+B.compLp u) (fun i ↦ (C i).compLp X+(D i).compLp u) X (η : Lp E 2 μ) := by
  obtain ⟨X,XT,hX,hXT,_⟩ := HilbertGlobalSolution.exists_section_solution b c
    (fun i ↦ (repaired_brownian hW i).toIsPreBrownianReal) (repaired_measurable hW)
    (repaired_continuous hW) i₀ T A B C D (0 : Ω → E) stronglyMeasurable_zero MemLp.zero u
  have hs := SectionDriverTransport.solution b
    (fun i ↦ (repaired_brownian hW i).toIsPreBrownianReal) (fun i ↦ (hW i).toIsPreBrownianReal)
    (repaired_measurable hW) hWm (fun i ↦ (hW i).mk_ae_forall_eq) T (0 : Ω → E) XT _ _ X hX
  let η := hXT.toLp XT
  have hη := SectionIntegralSolution.terminal_congr b (fun i ↦ (hW i).toIsPreBrownianReal)
    hWm T (0 : Ω → E) XT η _ X _ hs hXT.coeFn_toLp
  have hm := SectionTerminalSpace.SectionIntegralSolution.terminal_aestronglyMeasurable b
    (fun i ↦ (hW i).toIsPreBrownianReal) hWm T (0 : Ω → E) η _ X _ hη stronglyMeasurable_zero
  exact ⟨⟨η,hm⟩,X,hη⟩

/-- A genuine endpoint is selected; uniqueness will show the selection is
irrelevant. It is never an arbitrary abstract input-output map. -/
def terminal (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) : lpMeas E ℝ (𝓕 T) 2 μ :=
  (exists_terminal (𝓕:=𝓕) b c hW hWm i₀ T A B C D u).choose

theorem terminal_spec (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) :
    ∃ X : Lp E 2 (spacetimeMeasure 𝓕 μ T),
      SectionIntegralSolution b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T (0 : Ω → E)
        (A.compLp X+B.compLp u) (fun i ↦ (C i).compLp X+(D i).compLp u) X
        (terminal (𝓕:=𝓕) b c hW hWm i₀ T A B C D u : Lp E 2 μ) :=
  (exists_terminal (𝓕:=𝓕) b c hW hWm i₀ T A B C D u).choose_spec

theorem terminal_eq (u : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (η : Lp E 2 μ)
    (hX : SectionIntegralSolution b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T (0 : Ω → E)
      (A.compLp X+B.compLp u) (fun i ↦ (C i).compLp X+(D i).compLp u) X η) :
    (terminal (𝓕:=𝓕) b c hW hWm i₀ T A B C D u : Lp E 2 μ) = η := by
  obtain ⟨Y,hY⟩ := terminal_spec (𝓕:=𝓕) b c hW hWm i₀ T A B C D u
  apply Lp.ext
  exact HilbertBrownianUniqueness.terminal_unique b c hW hWm i₀ T A B C D
    (0 : Ω → E) stronglyMeasurable_zero MemLp.zero u Y X _ η hY hX

/-- Linearity follows by adding and scaling the actual integral solutions,
then identifying the resulting endpoint by true SDE uniqueness. -/
def terminalLinear : Lp U 2 (spacetimeMeasure 𝓕 μ T) →ₗ[ℝ] lpMeas E ℝ (𝓕 T) 2 μ where
  toFun := terminal (𝓕:=𝓕) b c hW hWm i₀ T A B C D
  map_add' u v := by
    obtain ⟨X,hX⟩ := terminal_spec (𝓕:=𝓕) b c hW hWm i₀ T A B C D u
    obtain ⟨Y,hY⟩ := terminal_spec (𝓕:=𝓕) b c hW hWm i₀ T A B C D v
    let η : Lp E 2 μ := terminal (𝓕:=𝓕) b c hW hWm i₀ T A B C D u
    let θ : Lp E 2 μ := terminal (𝓕:=𝓕) b c hW hWm i₀ T A B C D v
    have h := SectionIntegralSolution.add b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T 0 0
      (A.compLp X+B.compLp u) (A.compLp Y+B.compLp v) X Y
      (fun i ↦ (C i).compLp X+(D i).compLp u) (fun i ↦ (C i).compLp Y+(D i).compLp v) η θ hX hY
    have hd : A.compLp (X+Y)+B.compLp (u+v) =
        (A.compLp X+B.compLp u)+(A.compLp Y+B.compLp v) := by
      simp only [←ContinuousLinearMap.compLpₗ_apply,map_add]; abel
    have hz : (fun i ↦ (C i).compLp (X+Y)+(D i).compLp (u+v)) =
        (fun i ↦ (C i).compLp X+(D i).compLp u)+(fun i ↦ (C i).compLp Y+(D i).compLp v) := by
      funext i; simp only [Pi.add_apply,←ContinuousLinearMap.compLpₗ_apply,map_add]; abel
    rw [zero_add,←hd,←hz] at h
    have hh := SectionIntegralSolution.terminal_congr b (fun i ↦ (hW i).toIsPreBrownianReal)
      hWm T 0 (fun ω ↦ η ω+θ ω) (η+θ : Lp E 2 μ) _ _ _ h (Lp.coeFn_add η θ)
    apply Subtype.ext
    exact terminal_eq (𝓕:=𝓕) b c hW hWm i₀ T A B C D (u+v) (X+Y) (η+θ) hh
  map_smul' a u := by
    obtain ⟨X,hX⟩ := terminal_spec (𝓕:=𝓕) b c hW hWm i₀ T A B C D u
    let η : Lp E 2 μ := terminal (𝓕:=𝓕) b c hW hWm i₀ T A B C D u
    have h := SectionIntegralSolution.smul b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T a 0 η
      (A.compLp X+B.compLp u) X (fun i ↦ (C i).compLp X+(D i).compLp u) hX
    have hd : A.compLp (a • X)+B.compLp (a • u) = a • (A.compLp X+B.compLp u) := by
      simp only [←ContinuousLinearMap.compLpₗ_apply,map_smul,smul_add]
    have hz : (fun i ↦ (C i).compLp (a • X)+(D i).compLp (a • u)) =
        a • (fun i ↦ (C i).compLp X+(D i).compLp u) := by
      funext i; simp only [Pi.smul_apply,←ContinuousLinearMap.compLpₗ_apply,map_smul,smul_add]
    rw [smul_zero,←hd,←hz] at h
    have hh := SectionIntegralSolution.terminal_congr b (fun i ↦ (hW i).toIsPreBrownianReal)
      hWm T 0 (fun ω ↦ a • η ω) (a • η : Lp E 2 μ) _ _ _ h (Lp.coeFn_smul a η)
    apply Subtype.ext
    exact terminal_eq (𝓕:=𝓕) b c hW hWm i₀ T A B C D (a • u) (a • X) (a • η) hh

/-- A coefficient-only finite bound for the genuine terminal operator. -/
theorem terminalLinear_bounded : ∃ K : ℝ, ∀ u,
    ‖terminalLinear (𝓕:=𝓕) b c hW hWm i₀ T A B C D u‖ ≤ K*‖u‖ := by
  obtain ⟨K,_,hK⟩ := HilbertEndpointBound.terminal_bound (𝓕:=𝓕) b c hW hWm i₀ T A B C D
  refine ⟨K,?_⟩
  intro u
  obtain ⟨X,hX⟩ := terminal_spec (𝓕:=𝓕) b c hW hWm i₀ T A B C D u
  exact hK u X _ hX

/-- The actual continuous linear terminal control map. -/
def terminalCLM : Lp U 2 (spacetimeMeasure 𝓕 μ T) →L[ℝ] lpMeas E ℝ (𝓕 T) 2 μ :=
  (terminalLinear (𝓕:=𝓕) b c hW hWm i₀ T A B C D).mkContinuous
    (terminalLinear_bounded (𝓕:=𝓕) b c hW hWm i₀ T A B C D).choose
    (terminalLinear_bounded (𝓕:=𝓕) b c hW hWm i₀ T A B C D).choose_spec

/-- Exact controllability really implies surjectivity of this constructed
operator, retaining the paper's full F_T target space. -/
theorem surjective_of_exact
    (h : ActualControlProperties.Exact (𝓕:=𝓕) b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A B C D) :
    Function.Surjective (terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D) := by
  intro η
  obtain ⟨u,X,hX⟩ := h 0 η (lpMeas.aestronglyMeasurable η)
  refine ⟨u,?_⟩
  apply Subtype.ext
  exact terminal_eq (𝓕:=𝓕) b c hW hWm i₀ T A B C D u X η hX

end LinearStochastic.ActualTerminalOperator
