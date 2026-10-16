import LinearStochastic.HilbertSectionCoordinates
import LinearStochastic.CoordinatePathSolution
import LinearStochastic.CommonBrownianSections

/-! Every genuine Hilbert section solution is the same L² state and terminal
as a progressive continuous S² solution of the original equation. This closes
the analytic gap between section-based reachability and the paper's solution. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.HilbertBrownianRealization
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonVectorPicard CommonLocalSolution LpOrthonormalCoordinates
open VectorItoProduct LinearDuality SectionLinearDuality HilbertLocalSolution
open HilbertSectionCoordinates CoordinatePathSolution

variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (i₀ : ι) (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
  (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
  (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Ω → E)
  (hX : SectionIntegralSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ (A.compLp X+B.compLp u)
    (fun i => (C i).compLp X+(D i).compLp u) X XT)

/-- The actual scalar solution constructed from the supplied vector L² class. -/
def coordinateSolution : CommonSolutionData.Solution (𝓕:=𝓕) (fun i => (hW i).toIsPreBrownianReal) hWm T
    (coefficientMatrix b b A) (coefficientMatrix b c B)
    (fun i => coefficientMatrix b b (C i)) (fun i => coefficientMatrix b c (D i))
    (fun j ω => inner ℝ (b j) (ξ ω)) (fun j => coordinate c j u) :=
  CommonBrownianSections.ofSections hW hWm i₀ T _ _ _ _ _
    (fun j => (innerSL ℝ (b j)).continuous.comp_stronglyMeasurable hξ)
    (fun j => (innerSL ℝ (b j)).comp_memLp' hξ2) _ (fun j => coordinate b j X)
    (CommonSectionSolution.sections_of_real (fun i => (hW i).toIsPreBrownianReal) hWm T _ _ _ _ _ _ _ (fun j => by
      simpa only [drift_coordinates b c T A B u X,noise_coordinates b c T C D u X,innerSL_apply_apply] using
        sections_coordinates b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ XT _ _ X hX j))

/-- Endpoint identification uses the independent terminal integral equation. -/
theorem coordinateSolution_terminal (j : κ) :
    (fun ω => inner ℝ (b j) (XT ω)) =ᵐ[μ]
      (coordinateSolution b c hW hWm i₀ T A B C D ξ hξ hξ2 u X XT hX).path j T := by
  apply CommonBrownianSections.terminal_ofSections hW hWm i₀ T _ _ _ _ _ _ _ _ _ _
    (fun j ω => inner ℝ (b j) (XT ω)) _ j
  apply CommonSectionSolution.terminal_of_real (fun i => (hW i).toIsPreBrownianReal) hWm T
  intro a
  simpa only [drift_coordinates b c T A B u X,noise_coordinates b c T C D u X,innerSL_apply_apply] using
    terminal_coordinates b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ XT _ _ X hX a

include c i₀ hξ hξ2 hX in
/-- The output path R is progressive, continuous and S², represents the very
same input X in product measure, has the supplied initial and terminal values,
and solves the original actual integral equation at every time. -/
theorem exists_realization : ∃ R : ℝ≥0 → Ω → E,
    IsStronglyProgressive 𝓕 R ∧
    (∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T)) ∧
    MemLp (ContinuousDoobL2.pathSup R T) 2 μ ∧
    ((X : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R) ∧
    (R 0 =ᵐ[μ] ξ) ∧ (R T =ᵐ[μ] XT) ∧
    (∀ t, t ≤ T → R t =ᵐ[μ] integralState b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ (A.compLp X+B.compLp u)
      (fun i => (C i).compLp X+(D i).compLp u) (t:ℝ)) := by
  let q := coordinateSolution b c hW hWm i₀ T A B C D ξ hξ hξ2 u X XT hX
  have hq : assemble (mΛ:=𝓕.predictable) b q.X = X := assemble_coordinates (mΛ:=𝓕.predictable) b X
  have hspace : ((X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) : ℝ≥0 × Ω → E)
      =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry (reconstruct b q.path) := by
    have hall : ∀ᵐ z ∂(CommonItoCLM.timeMeasure_T T).prod μ, ∀ j, q.X j z = q.path j z.1 z.2 := by
      rw [ae_all_iff]; exact q.representative
    have ha := ae_of_ae_trim 𝓕.predictable_le_prod (assemble_ae (mΛ:=𝓕.predictable) b q.X)
    rw [hq] at ha
    filter_upwards [ha,hall] with z ha hq
    rw [ha]
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun x : ℝ => x • b j) (hq j))
  have hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => reconstruct b q.path t ω) (Iic T) := by
    have hall : ∀ᵐ ω ∂μ, ∀ j, ContinuousOn (fun t => q.path j t ω) (Iic T) := by
      rw [ae_all_iff]; exact q.continuous
    filter_upwards [hall] with ω hω
    exact continuousOn_finsetSum _ (fun j _ => (hω j).smul continuousOn_const)
  have hstart : reconstruct b q.path 0 =ᵐ[μ] ξ := by
    have hall : ∀ᵐ ω ∂μ, ∀ j, q.path j 0 ω = inner ℝ (b j) (ξ ω) := by
      rw [ae_all_iff]; exact q.initial
    filter_upwards [hall] with ω hω
    simpa only [reconstruct,hω] using b.sum_repr' (ξ ω)
  have hend : reconstruct b q.path T =ᵐ[μ] XT := by
    have hall : ∀ᵐ ω ∂μ, ∀ j, q.path j T ω = inner ℝ (b j) (XT ω) := by
      rw [ae_all_iff]
      exact fun j => (coordinateSolution_terminal b c hW hWm i₀ T A B C D ξ hξ hξ2 u X XT hX j).symm
    filter_upwards [hall] with ω hω
    simpa only [reconstruct,hω] using b.sum_repr' (XT ω)
  refine ⟨reconstruct b q.path,reconstruct_progressive b q.path
    (fun j => (q.progressive j).isStronglyProgressive),hc,
    reconstruct_S2 b T q.path (fun j => (q.progressive j).isStronglyProgressive) q.continuous q.squareSup,
    hspace,hstart,hend,?_⟩
  intro t ht
  have he := integral_ae b (fun i => (hW i).toIsPreBrownianReal) hWm T t ht _ _ _ q.path q.equation
  have hξeq : (fun ω => ∑ j, inner ℝ (b j) (ξ ω) • b j) = ξ := funext (fun ω => b.sum_repr' (ξ ω))
  have hd := assemble_driftInput b c T A B (fun j => coordinate c j u) q.X
  rw [hq,assemble_coordinates (mΛ:=𝓕.predictable)] at hd
  have hz : (fun i => assemble (mΛ:=𝓕.predictable) b
      (noiseInput T (fun i => coefficientMatrix b b (C i)) (fun i => coefficientMatrix b c (D i))
        (fun j => coordinate c j u) q.X i)) = fun i => (C i).compLp X+(D i).compLp u := by
    funext i
    rw [assemble_noiseInput,hq,assemble_coordinates (mΛ:=𝓕.predictable)]
  rw [hξeq,hd,hz] at he
  exact he

end LinearStochastic.HilbertBrownianRealization
