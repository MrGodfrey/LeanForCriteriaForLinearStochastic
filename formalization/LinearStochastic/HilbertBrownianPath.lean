module

public import LinearStochastic.CoordinatePathSolution
public import LinearStochastic.CommonBrownianGlobal
public import LinearStochastic.SectionTerminalSpace

@[expose] public section

/-! Arbitrary finite-horizon existence for the original Hilbert coefficient
maps, obtained from actual globally pasted coordinate SDE solutions. -/
noncomputable section
namespace LinearStochastic.HilbertBrownianPath
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonVectorPicard CommonLocalSolution LpOrthonormalCoordinates
open HilbertLocalSolution CoordinatePathSolution LinearDuality SectionLinearDuality

variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι]
  (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))


include c in
/-- Every horizon has a genuine progressive continuous S² Hilbert solution,
with the original coefficient maps and true integral equation at every time.
The continuity, original product-measure representative and initial value
refer to the very same output path R, not to an unlinked modification.
There is no short-horizon, all-sample continuity or solution-existence premise. -/
theorem exists_full_solution (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) :
    ∃ (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (R : ℝ≥0 → Ω → E),
      IsStronglyProgressive 𝓕 R ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Set.Iic T)) ∧
      MemLp (ContinuousDoobL2.pathSup R T) 2 μ ∧
      ((X : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R) ∧
      (R 0 =ᵐ[μ] ξ) ∧
      SectionIntegralSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ (A.compLp X+B.compLp u)
        (fun i => (C i).compLp X+(D i).compLp u) X (R T) ∧
      Nonempty (ContinuousRealization T ξ X (R T)) ∧
      (∀ t, t ≤ T → R t =ᵐ[μ] integralState b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ (A.compLp X+B.compLp u)
        (fun i => (C i).compLp X+(D i).compLp u) (t:ℝ)) := by
  let a := coefficientMatrix b b A
  let β := coefficientMatrix b c B
  let γ := fun i => coefficientMatrix b b (C i)
  let δ := fun i => coefficientMatrix b c (D i)
  let η := fun j ω => inner ℝ (b j) (ξ ω)
  have hη (j : κ) : StronglyMeasurable[𝓕 0] (η j) :=
    (innerSL ℝ (b j)).continuous.comp_stronglyMeasurable hξ
  have hη2 (j : κ) : MemLp (η j) 2 μ := (innerSL ℝ (b j)).comp_memLp' hξ2
  let v := fun j => VectorItoProduct.coordinate c j u
  obtain ⟨q⟩ := CommonBrownianGlobal.exists_global hW hWm i₀ T a β γ δ η hη hη2 v
  let f := driftInput T a β v q.X
  let φ := noiseInput T γ δ v q.X
  have hs := section_solution b (fun i => (hW i).toIsPreBrownianReal) hWm T η f φ q.X q.path q.representative q.equation
  have hr := continuousRealization b T η q.X q.path q.representative q.continuous q.initial
  have hηeq : (fun ω => ∑ j, η j ω • b j) = ξ := funext (fun ω => b.sum_repr' (ξ ω))
  have hv : assemble (mΛ:=𝓕.predictable) c v = u := assemble_coordinates (mΛ:=𝓕.predictable) c u
  have hf : assemble (mΛ:=𝓕.predictable) b f =
      A.compLp (assemble (mΛ:=𝓕.predictable) b q.X)+B.compLp u := by
    rw [show f = driftInput T (coefficientMatrix b b A) (coefficientMatrix b c B) v q.X from rfl,
      assemble_driftInput,hv]
  have hφ : (fun i => assemble (mΛ:=𝓕.predictable) b (φ i)) =
      fun i => (C i).compLp (assemble (mΛ:=𝓕.predictable) b q.X)+(D i).compLp u := by
    funext i
    rw [show φ i = noiseInput T (fun i => coefficientMatrix b b (C i))
      (fun i => coefficientMatrix b c (D i)) v q.X i from rfl,assemble_noiseInput,hv]
  rw [hηeq,hf,hφ] at hs
  rw [hηeq] at hr
  have hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => reconstruct b q.path t ω) (Set.Iic T) := by
    have hall : ∀ᵐ ω ∂μ, ∀ j, ContinuousOn (fun t => q.path j t ω) (Set.Iic T) := by
      rw [ae_all_iff]; exact q.continuous
    filter_upwards [hall] with ω hω
    exact continuousOn_finsetSum _ (fun j _ => (hω j).smul continuousOn_const)
  have hspace : ((assemble (mΛ:=𝓕.predictable) b q.X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) : ℝ≥0 × Ω → E)
      =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry (reconstruct b q.path) := by
    have hall : ∀ᵐ z ∂(CommonItoCLM.timeMeasure_T T).prod μ, ∀ j, q.X j z = q.path j z.1 z.2 := by
      rw [ae_all_iff]; exact q.representative
    filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod (assemble_ae (mΛ:=𝓕.predictable) b q.X),hall]
      with z ha hq
    rw [ha]
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun x : ℝ => x • b j) (hq j))
  have hinitial : reconstruct b q.path 0 =ᵐ[μ] ξ := by
    have hall : ∀ᵐ ω ∂μ, ∀ j, q.path j 0 ω = η j ω := by
      rw [ae_all_iff]; exact q.initial
    filter_upwards [hall] with ω hω
    simpa only [reconstruct,hω,η] using b.sum_repr' (ξ ω)
  refine ⟨assemble (mΛ:=𝓕.predictable) b q.X,reconstruct b q.path,
    reconstruct_progressive b q.path (fun j => (q.progressive j).isStronglyProgressive),hcont,
    reconstruct_S2 b T q.path (fun j => (q.progressive j).isStronglyProgressive) q.continuous q.squareSup,
    hspace,hinitial,hs,⟨hr⟩,?_⟩
  intro t ht
  have he := integral_ae b (fun i => (hW i).toIsPreBrownianReal) hWm T t ht η f φ q.path q.equation
  rw [hηeq,hf,hφ] at he
  exact he

end LinearStochastic.HilbertBrownianPath
