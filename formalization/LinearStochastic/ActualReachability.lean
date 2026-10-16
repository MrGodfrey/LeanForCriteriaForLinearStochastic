import LinearStochastic.SectionSolutionLinearity
import LinearStochastic.SectionTerminalSpace

/-! Reachable terminals of the genuine forward stochastic equation form a
linear subspace of the actual terminal L² space. -/
noncomputable section
namespace LinearStochastic.ActualReachability
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality

variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- The elements are actual terminal L² classes reached from zero, with an
actual predictable control and an actual sectionwise integral solution. -/
def terminals (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E) : Submodule ℝ (Lp E 2 μ) where
  carrier := {η | ∃ (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)),
    SectionIntegralSolution b hW hWm T 0 (A.compLp X+B.compLp u)
      (fun i => (C i).compLp X+(D i).compLp u) X η}
  zero_mem' := by
    refine ⟨0,0,?_⟩
    have h := SectionSolutionLinearity.zero_solution (𝓕:=𝓕) b hW hWm T
    have h' := SectionSolutionLinearity.SectionIntegralSolution.terminal_congr b hW hWm
      T 0 0 (0 : Lp E 2 μ) 0 0 (fun _ => 0) h (Lp.coeFn_zero E 2 μ)
    simpa only [← ContinuousLinearMap.compLpₗ_apply,map_zero,add_zero] using h'
  add_mem' := by
    rintro η θ ⟨u,X,hX⟩ ⟨v,Y,hY⟩
    refine ⟨u+v,X+Y,?_⟩
    have h := SectionSolutionLinearity.SectionIntegralSolution.add b hW hWm T 0 0
      (A.compLp X+B.compLp u) (A.compLp Y+B.compLp v) X Y
      (fun i => (C i).compLp X+(D i).compLp u)
      (fun i => (C i).compLp Y+(D i).compLp v) η θ hX hY
    have hd : A.compLp (X+Y)+B.compLp (u+v) =
        (A.compLp X+B.compLp u)+(A.compLp Y+B.compLp v) := by
      simp only [← ContinuousLinearMap.compLpₗ_apply,map_add]
      abel
    have hz : (fun i => (C i).compLp (X+Y)+(D i).compLp (u+v)) =
        (fun i => (C i).compLp X+(D i).compLp u)+(fun i => (C i).compLp Y+(D i).compLp v) := by
      funext i
      simp only [Pi.add_apply,← ContinuousLinearMap.compLpₗ_apply,map_add]
      abel
    rw [zero_add,←hd,←hz] at h
    exact SectionSolutionLinearity.SectionIntegralSolution.terminal_congr b hW hWm T 0
      (fun ω => η ω+θ ω) (η+θ : Lp E 2 μ) _ _ _ h (Lp.coeFn_add η θ)
  smul_mem' := by
    rintro a η ⟨u,X,hX⟩
    refine ⟨a • u,a • X,?_⟩
    have h := SectionSolutionLinearity.SectionIntegralSolution.smul b hW hWm T a 0 η
      (A.compLp X+B.compLp u) X (fun i => (C i).compLp X+(D i).compLp u) hX
    have hd : A.compLp (a • X)+B.compLp (a • u) = a • (A.compLp X+B.compLp u) := by
      simp only [← ContinuousLinearMap.compLpₗ_apply,map_smul,smul_add]
    have hz : (fun i => (C i).compLp (a • X)+(D i).compLp (a • u)) =
        a • (fun i => (C i).compLp X+(D i).compLp u) := by
      funext i
      simp only [Pi.smul_apply,← ContinuousLinearMap.compLpₗ_apply,map_smul,smul_add]
    rw [smul_zero,←hd,←hz] at h
    exact SectionSolutionLinearity.SectionIntegralSolution.terminal_congr b hW hWm T 0
      (fun ω => a • η ω) (a • η : Lp E 2 μ) _ _ _ h (Lp.coeFn_smul a η)

/-- Every genuinely reachable terminal belongs to the original F_T L² space. -/
theorem terminals_le_terminalSpace (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E) :
    terminals (𝓕:=𝓕) b hW hWm T A B C D ≤ lpMeas E ℝ (𝓕 T) 2 μ := by
  rintro η ⟨u,X,hX⟩
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  exact SectionTerminalSpace.SectionIntegralSolution.terminal_aestronglyMeasurable b hW hWm T 0 η
    _ X _ hX stronglyMeasurable_zero

end LinearStochastic.ActualReachability
