import LinearStochastic.CoordinatePathSolution
import LinearStochastic.CommonGlobalExistence
import LinearStochastic.SectionTerminalSpace

/-! Arbitrary finite-horizon existence for the original Hilbert coefficient
maps, obtained from actual globally pasted coordinate SDE solutions. -/
noncomputable section
namespace LinearStochastic.HilbertGlobalSolution
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
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

include c hWc in
/-- Every horizon has a genuine progressive continuous S² Hilbert solution,
with the original coefficient maps and true integral equation at every time.
There is no short-horizon or solution-existence premise. -/
theorem exists_full_solution (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) :
    ∃ (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (R : ℝ≥0 → Ω → E),
      IsStronglyProgressive 𝓕 R ∧ MemLp (ContinuousDoobL2.pathSup R T) 2 μ ∧
      SectionIntegralSolution b hW hWm T ξ (A.compLp X+B.compLp u)
        (fun i => (C i).compLp X+(D i).compLp u) X (R T) ∧
      Nonempty (ContinuousRealization T ξ X (R T)) ∧
      (∀ t, t ≤ T → R t =ᵐ[μ] integralState b hW hWm T ξ (A.compLp X+B.compLp u)
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
  obtain ⟨q⟩ := CommonGlobalExistence.exists_global hW hWm hWc i₀ T a β γ δ η hη hη2 v
  let f := driftInput T a β v q.X
  let φ := noiseInput T γ δ v q.X
  have hs := section_solution b hW hWm T η f φ q.X q.path q.representative q.equation
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
  refine ⟨assemble (mΛ:=𝓕.predictable) b q.X,reconstruct b q.path,
    reconstruct_progressive b q.path (fun j => (q.progressive j).isStronglyProgressive),
    reconstruct_S2 b T q.path (fun j => (q.progressive j).isStronglyProgressive) q.continuous q.squareSup,
    hs,⟨hr⟩,?_⟩
  intro t ht
  have he := integral_ae b hW hWm T t ht η f φ q.path q.equation
  rw [hηeq,hf,hφ] at he
  exact he

include c hWc in
/-- The actual global solution supplies the section interface and its genuine
L² terminal and continuous realization on every prescribed finite horizon. -/
theorem exists_section_solution (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) :
    ∃ (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Ω → E),
      SectionIntegralSolution b hW hWm T ξ (A.compLp X+B.compLp u)
        (fun i => (C i).compLp X+(D i).compLp u) X XT ∧
      MemLp XT 2 μ ∧ Nonempty (ContinuousRealization T ξ X XT) := by
  obtain ⟨X,R,_,_,hs,hr,_⟩ := exists_full_solution b c hW hWm hWc i₀ T A B C D ξ hξ hξ2 u
  exact ⟨X,R T,hs,SectionTerminalSpace.SectionIntegralSolution.terminal_memLp b hW hWm T ξ (R T)
    _ X _ hs hξ2,hr⟩

end LinearStochastic.HilbertGlobalSolution
