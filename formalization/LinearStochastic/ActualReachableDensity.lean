import LinearStochastic.ActualReachability
import LinearStochastic.ActualObservationDuality
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! The actual reachable subspace in the true F_T L² Hilbert space, its
orthogonal complement, and the exact approximation consequence of density. -/
noncomputable section
namespace LinearStochastic.ActualReachableDensity
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality ActualReachability ActualObservationDuality

variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Reachability regarded inside the original terminal-measurable Hilbert
space. This is the actual reachable subspace, not its linear span. -/
def relativeTerminals (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E) :
    Submodule ℝ (lpMeas E ℝ (𝓕 T) 2 μ) :=
  (terminals (𝓕:=𝓕) b hW hWm T A B C D).comap (lpMeas E ℝ (𝓕 T) 2 μ).subtype

omit [CompleteSpace U] in
/-- Its true Hilbert orthogonal complement is exactly the annihilator of
actual forward terminals, including arbitrary raw endpoint representatives. -/
theorem orthogonal_iff_annihilates (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E) (η : lpMeas E ℝ (𝓕 T) 2 μ) :
    η ∈ (relativeTerminals (𝓕:=𝓕) b hW hWm T A B C D).orthogonal ↔
      AnnihilatesForwardTerminals (𝓕:=𝓕) b hW hWm T A B C D (η : Lp E 2 μ) := by
  constructor
  · intro hη u X XT hX
    have hXT := SectionTerminalSpace.SectionIntegralSolution.terminal_memLp b hW hWm T 0 XT
      _ X _ hX MemLp.zero
    let ξ := hXT.toLp XT
    have hξR : ξ ∈ terminals (𝓕:=𝓕) b hW hWm T A B C D := by
      refine ⟨u,X,?_⟩
      exact SectionSolutionLinearity.SectionIntegralSolution.terminal_congr b hW hWm T 0 XT ξ
        _ X _ hX hXT.coeFn_toLp
    have hξM := terminals_le_terminalSpace (𝓕:=𝓕) b hW hWm T A B C D hξR
    have hi := hη ⟨ξ,hξM⟩ hξR
    change inner ℝ ξ (η : Lp E 2 μ) = 0 at hi
    rw [L2.inner_def] at hi
    rw [←hi]
    apply integral_congr_ae
    filter_upwards [hXT.coeFn_toLp] with ω he
    rw [he]
  · intro hη ξ hξ
    obtain ⟨u,X,hX⟩ := hξ
    change inner ℝ (ξ : Lp E 2 μ) (η : Lp E 2 μ) = 0
    rw [L2.inner_def]
    exact hη u X ξ hX

omit [CompleteSpace U] in
/-- Vanishing of actual terminal annihilators implies density of the actual
reachable set, using completeness of the genuine F_T L² space. -/
theorem dense_of_annihilator_zero (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hzero : ∀ η : Lp E 2 μ, AEStronglyMeasurable[𝓕 T] η μ →
      AnnihilatesForwardTerminals (𝓕:=𝓕) b hW hWm T A B C D η → η = 0) :
    Dense (relativeTerminals (𝓕:=𝓕) b hW hWm T A B C D : Set (lpMeas E ℝ (𝓕 T) 2 μ)) := by
  letI : Fact (𝓕 T ≤ mΩ) := ⟨𝓕.le T⟩
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply (Submodule.eq_bot_iff _).mpr
  intro η hη
  apply Subtype.ext
  exact hzero η (lpMeas.aestronglyMeasurable η)
    ((orthogonal_iff_annihilates b hW hWm T A B C D η).mp hη)

omit [CompleteSpace U] in
/-- Density gives the exact squared L² error requested in approximate
controllability, with a true original control and a true forward solution. -/
theorem approximation_of_dense (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hd : Dense (relativeTerminals (𝓕:=𝓕) b hW hWm T A B C D : Set (lpMeas E ℝ (𝓕 T) 2 μ)))
    (η : Lp E 2 μ) (hη : AEStronglyMeasurable[𝓕 T] η μ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Lp E 2 μ),
      SectionIntegralSolution b hW hWm T 0 (A.compLp X+B.compLp u)
        (fun i => (C i).compLp X+(D i).compLp u) X XT ∧ ‖XT-η‖^2 < ε := by
  let y : lpMeas E ℝ (𝓕 T) 2 μ := ⟨η,hη⟩
  obtain ⟨x,hx,hclose⟩ := (Metric.mem_closure_iff.mp (hd y)) (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  obtain ⟨u,X,hX⟩ := hx
  refine ⟨u,X,x,hX,?_⟩
  have hnorm : ‖(x : Lp E 2 μ)-η‖ < Real.sqrt ε := by
    rw [dist_eq_norm] at hclose
    change ‖η-(x : Lp E 2 μ)‖ < Real.sqrt ε at hclose
    simpa only [norm_sub_rev] using hclose
  nlinarith [Real.sq_sqrt hε.le,norm_nonneg ((x : Lp E 2 μ)-η)]

end LinearStochastic.ActualReachableDensity
