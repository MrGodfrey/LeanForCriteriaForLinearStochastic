module

public import LinearStochastic.ActualReachableDensity
public import LinearStochastic.HilbertGlobalSolution

@[expose] public section

/-! Approximation from arbitrary actual F₀ L² initial data, using density of
the actual zero-initial reachable subspace and a genuinely constructed forward
solution. No abstract terminal-map linearity is assumed. -/
noncomputable section
namespace LinearStochastic.ActualApproximation
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality ActualReachability ActualReachableDensity

variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

include c hWc in
/-- Density yields a genuine controlled solution whose squared terminal L²
error is below ε, from every original F₀-measurable square-integrable initial
state and for every original F_T-measurable target. -/
theorem approximation_from_initial (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hd : Dense (relativeTerminals (𝓕:=𝓕) b hW hWm T A B C D : Set (lpMeas E ℝ (𝓕 T) 2 μ)))
    (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (η : Lp E 2 μ) (hη : AEStronglyMeasurable[𝓕 T] η μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Lp E 2 μ),
      SectionIntegralSolution b hW hWm T ξ (A.compLp X+B.compLp u)
        (fun i => (C i).compLp X+(D i).compLp u) X XT ∧ ‖XT-η‖^2 < ε := by
  obtain ⟨X₀,XT₀,hX₀,hXT₀,_⟩ := HilbertGlobalSolution.exists_section_solution b c hW hWm hWc i₀ T
    A B C D ξ hξ hξ2 0
  let ρ := hXT₀.toLp XT₀
  have hρ : AEStronglyMeasurable[𝓕 T] ρ μ :=
    (SectionTerminalSpace.SectionIntegralSolution.terminal_aestronglyMeasurable b hW hWm T ξ XT₀
      _ X₀ _ hX₀ hξ).congr hXT₀.coeFn_toLp.symm
  have hηρ : AEStronglyMeasurable[𝓕 T] (η-ρ : Lp E 2 μ) μ :=
    (hη.sub hρ).congr (Lp.coeFn_sub η ρ).symm
  obtain ⟨u,X₁,XT₁,hX₁,herr⟩ := approximation_of_dense b hW hWm T A B C D hd (η-ρ) hηρ ε hε
  have hX₀' := SectionSolutionLinearity.SectionIntegralSolution.terminal_congr b hW hWm T ξ XT₀ ρ
    _ X₀ _ hX₀ hXT₀.coeFn_toLp
  have hsum := SectionSolutionLinearity.SectionIntegralSolution.add b hW hWm T ξ 0
    (A.compLp X₀+B.compLp (0 : Lp U 2 (spacetimeMeasure 𝓕 μ T))) (A.compLp X₁+B.compLp u) X₀ X₁
    (fun i => (C i).compLp X₀+(D i).compLp (0 : Lp U 2 (spacetimeMeasure 𝓕 μ T)))
    (fun i => (C i).compLp X₁+(D i).compLp u) ρ XT₁ hX₀' hX₁
  have hd' : A.compLp (X₀+X₁)+B.compLp u =
      (A.compLp X₀+B.compLp (0 : Lp U 2 (spacetimeMeasure 𝓕 μ T)))+(A.compLp X₁+B.compLp u) := by
    simp only [← ContinuousLinearMap.compLpₗ_apply,map_zero,map_add,add_zero]
    abel
  have hz' : (fun i => (C i).compLp (X₀+X₁)+(D i).compLp u) =
      (fun i => (C i).compLp X₀+(D i).compLp (0 : Lp U 2 (spacetimeMeasure 𝓕 μ T)))+(fun i => (C i).compLp X₁+(D i).compLp u) := by
    funext i
    simp only [Pi.add_apply,← ContinuousLinearMap.compLpₗ_apply,map_zero,map_add,add_zero]
    abel
  rw [add_zero,←hd',←hz'] at hsum
  refine ⟨u,X₀+X₁,ρ+XT₁,?_,?_⟩
  · exact SectionSolutionLinearity.SectionIntegralSolution.terminal_congr b hW hWm T ξ
      (fun ω => ρ ω+XT₁ ω) (ρ+XT₁ : Lp E 2 μ) _ _ _ hsum (Lp.coeFn_add ρ XT₁)
  · rwa [show ρ+XT₁-η = XT₁-(η-ρ) from by abel]

end LinearStochastic.ActualApproximation
