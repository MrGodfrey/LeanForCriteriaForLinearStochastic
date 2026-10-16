import LinearStochastic.ActualTerminalDensity
import LinearStochastic.RawExactProperties

/-! Actual initial-state null controllability is exactly membership of the
negative uncontrolled endpoint in the terminal map's range or its closure. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.ActualNullRange
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
open CommonItoMultichannel SectionLinearDuality SectionSolutionLinearity ActualTerminalOperator CommonBrownianRepair
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (i₀ : ι) (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
local instance terminalFact : Fact (𝓕 T ≤ mΩ) := ⟨𝓕.le T⟩

include c i₀ in
/-- The uncontrolled endpoint used below genuinely exists in the original
terminal sigma algebra, for every deterministic initial vector. -/
theorem exists_uncontrolled (v : E) :
    ∃ (η : lpMeas E ℝ (𝓕 T) 2 μ) (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)),
      ActualControlProperties.ControlledTerminal (𝓕:=𝓕) b
        (fun i=>(hW i).toIsPreBrownianReal) hWm T A B C D v 0 Y η := by
  obtain ⟨X,XT,hX,hXT,_⟩ := HilbertGlobalSolution.exists_section_solution (𝓕:=𝓕) b c
    (fun i=>(repaired_brownian hW i).toIsPreBrownianReal) (repaired_measurable hW)
    (repaired_continuous hW) i₀ T A B C D (fun _=>v) stronglyMeasurable_const (memLp_const v) 0
  have hs := SectionDriverTransport.solution b
    (fun i=>(repaired_brownian hW i).toIsPreBrownianReal) (fun i=>(hW i).toIsPreBrownianReal)
    (repaired_measurable hW) hWm (fun i=>(hW i).mk_ae_forall_eq) T (fun _=>v) XT _ _ X hX
  let η := hXT.toLp XT
  have hη := SectionIntegralSolution.terminal_congr b (fun i=>(hW i).toIsPreBrownianReal)
    hWm T (fun _=>v) XT η _ X _ hs hXT.coeFn_toLp
  have hm := SectionTerminalSpace.SectionIntegralSolution.terminal_aestronglyMeasurable b
    (fun i=>(hW i).toIsPreBrownianReal) hWm T (fun _=>v) η _ X _ hη stronglyMeasurable_const
  exact ⟨⟨η,hm⟩,X,hη⟩

/-- Actual superposition with an uncontrolled trajectory gives a genuine
controlled trajectory whose endpoint is the affine terminal-map expression. -/
theorem affine_solution (v : E) (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (η : lpMeas E ℝ (𝓕 T) 2 μ)
    (hY : ActualControlProperties.ControlledTerminal (𝓕:=𝓕) b
      (fun i=>(hW i).toIsPreBrownianReal) hWm T A B C D v 0 Y η)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) :
    ∃ X, ActualControlProperties.ControlledTerminal (𝓕:=𝓕) b
      (fun i=>(hW i).toIsPreBrownianReal) hWm T A B C D v u X
      ((η + terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D u : lpMeas E ℝ (𝓕 T) 2 μ) : Lp E 2 μ) := by
  obtain ⟨X,hX⟩ := terminal_spec (𝓕:=𝓕) b c hW hWm i₀ T A B C D u
  let θ : Lp E 2 μ := terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D u
  have h := SectionIntegralSolution.add b (fun i=>(hW i).toIsPreBrownianReal) hWm T
    (fun _=>v) 0 (A.compLp Y+B.compLp (0 : Lp U 2 (spacetimeMeasure 𝓕 μ T))) (A.compLp X+B.compLp u) Y X
    (fun i=>(C i).compLp Y+(D i).compLp (0 : Lp U 2 (spacetimeMeasure 𝓕 μ T)))
    (fun i=>(C i).compLp X+(D i).compLp u) (η:Lp E 2 μ) θ hY hX
  have hd : (A.compLp Y+B.compLp (0 : Lp U 2 (spacetimeMeasure 𝓕 μ T)))+(A.compLp X+B.compLp u)=A.compLp (Y+X)+B.compLp u := by
    simp only [←ContinuousLinearMap.compLpₗ_apply,map_zero,map_add]; abel
  have hn : (fun i=>(C i).compLp Y+(D i).compLp (0 : Lp U 2 (spacetimeMeasure 𝓕 μ T)))+
      (fun i=>(C i).compLp X+(D i).compLp u)=fun i=>(C i).compLp (Y+X)+(D i).compLp u := by
    funext i
    simp only [Pi.add_apply,←ContinuousLinearMap.compLpₗ_apply,map_zero,map_add]; abel
  rw [add_zero,hd,hn] at h
  refine ⟨Y+X,SectionIntegralSolution.terminal_congr b (fun i=>(hW i).toIsPreBrownianReal)
    hWm T (fun _=>v) ((η:Lp E 2 μ)+θ : Ω→E) ((η:Lp E 2 μ)+θ : Lp E 2 μ) _ _ _ h ?_⟩
  exact Lp.coeFn_add (η:Lp E 2 μ) θ

/-- The affine expression identifies every actual solution endpoint by
proved global uniqueness, not by selecting a canonical subclass. -/
theorem endpoint_eq (v : E) (Y X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (η : lpMeas E ℝ (𝓕 T) 2 μ) (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (XT : Lp E 2 μ)
    (hY : ActualControlProperties.ControlledTerminal (𝓕:=𝓕) b
      (fun i=>(hW i).toIsPreBrownianReal) hWm T A B C D v 0 Y η)
    (hX : ActualControlProperties.ControlledTerminal (𝓕:=𝓕) b
      (fun i=>(hW i).toIsPreBrownianReal) hWm T A B C D v u X XT) :
    XT=(η:Lp E 2 μ)+(terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D u : Lp E 2 μ) := by
  obtain ⟨Z,hZ⟩ := affine_solution b c hW hWm i₀ T A B C D v Y η hY u
  apply Lp.ext
  exact HilbertBrownianUniqueness.terminal_unique b c hW hWm i₀ T A B C D
    (fun _=>v) stronglyMeasurable_const (memLp_const v) u X Z XT _ hX hZ

/-- Exact null reachability of a fixed initial state is precisely range
membership of the negative actual uncontrolled endpoint. -/
theorem exact_iff_range (v : E) (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (η : lpMeas E ℝ (𝓕 T) 2 μ)
    (hY : ActualControlProperties.ControlledTerminal (𝓕:=𝓕) b
      (fun i=>(hW i).toIsPreBrownianReal) hWm T A B C D v 0 Y η) :
    (∃ u X, ActualControlProperties.ControlledTerminal (𝓕:=𝓕) b
      (fun i=>(hW i).toIsPreBrownianReal) hWm T A B C D v u X 0) ↔
      -η ∈ Set.range (terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D) := by
  constructor
  · rintro ⟨u,X,hX⟩
    refine ⟨u,Subtype.ext ?_⟩
    have he := endpoint_eq b c hW hWm i₀ T A B C D v Y X η u 0 hY hX
    change (terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D u : Lp E 2 μ)=-(η:Lp E 2 μ)
    exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using he.symm)
  · rintro ⟨u,hu⟩
    obtain ⟨X,hX⟩ := affine_solution b c hW hWm i₀ T A B C D v Y η hY u
    rw [hu,add_neg_cancel] at hX
    exact ⟨u,X,hX⟩

/-- Approximate null reachability is precisely the corresponding closure
membership, with the manuscript's squared L² error. -/
theorem approximate_iff_closure (v : E) (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (η : lpMeas E ℝ (𝓕 T) 2 μ)
    (hY : ActualControlProperties.ControlledTerminal (𝓕:=𝓕) b
      (fun i=>(hW i).toIsPreBrownianReal) hWm T A B C D v 0 Y η) :
    (∀ ε : ℝ, 0<ε → ∃ u X XT, ActualControlProperties.ControlledTerminal (𝓕:=𝓕) b
      (fun i=>(hW i).toIsPreBrownianReal) hWm T A B C D v u X XT ∧ ‖XT‖^2<ε) ↔
      -η ∈ closure (Set.range (terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D)) := by
  rw [Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨u,X,XT,hX,he⟩ := h (ε^2) (sq_pos_of_pos hε)
    refine ⟨terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D u,⟨u,rfl⟩,?_⟩
    rw [dist_comm,dist_eq_norm,sub_neg_eq_add,add_comm]
    change ‖(η:Lp E 2 μ)+(terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D u : Lp E 2 μ)‖<ε
    rw [←endpoint_eq b c hW hWm i₀ T A B C D v Y X η u XT hY hX]
    nlinarith [norm_nonneg XT]
  · intro h ε hε
    obtain ⟨θ,⟨u,rfl⟩,hu⟩ := h (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    obtain ⟨X,hX⟩ := affine_solution b c hW hWm i₀ T A B C D v Y η hY u
    refine ⟨u,X,_,hX,?_⟩
    rw [dist_comm,dist_eq_norm,sub_neg_eq_add,add_comm] at hu
    change ‖(η:Lp E 2 μ)+(terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D u : Lp E 2 μ)‖<Real.sqrt ε at hu
    change ‖(η:Lp E 2 μ)+(terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D u : Lp E 2 μ)‖^2<ε
    nlinarith [Real.sq_sqrt hε.le,norm_nonneg ((η:Lp E 2 μ)+(terminalCLM (𝓕:=𝓕) b c hW hWm i₀ T A B C D u : Lp E 2 μ))]
end LinearStochastic.ActualNullRange
