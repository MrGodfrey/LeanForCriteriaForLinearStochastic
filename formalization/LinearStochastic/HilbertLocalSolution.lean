import LinearStochastic.CoordinateSectionSolution
import LinearStochastic.BSDETerminal

/-! The genuinely constructed coordinate Picard solution is transported to
the original Hilbert-valued coefficient maps and the actual integral interface. -/
noncomputable section
namespace LinearStochastic.HilbertLocalSolution
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonVectorPicard CommonInitialPredictable CommonLocalSolution
open LpOrthonormalCoordinates CoordinateIntegralReconstruction CoordinateSectionSolution
open LinearDuality SectionLinearDuality

section Coordinates
variable {Λ E U κ τ : Type*} [mΛ : MeasurableSpace Λ] {ν : Measure Λ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [Fintype κ] [Fintype τ]

def coefficientMatrix (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
    (L : U →L[ℝ] E) : Matrix κ τ ℝ := fun a j => inner ℝ (b a) (L (c j))

theorem assemble_add (b : OrthonormalBasis κ ℝ E) (f g : κ → Lp ℝ 2 ν) :
    assemble b (f + g) = assemble b f + assemble b g := by
  simp only [assemble,Pi.add_apply,map_add,Finset.sum_add_distrib]
end Coordinates

section Coefficients
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι]
  {𝓕 : Filtration ℝ≥0 mΩ}
  (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)

omit [IsProbabilityMeasure μ] in
theorem assemble_matrixAction (T : ℝ≥0) (L : U →L[ℝ] E) (u : τ → H2 𝓕 μ T) :
    assemble (mΛ := 𝓕.predictable) b (matrixAction T (coefficientMatrix b c L) u) =
      L.compLp (assemble (mΛ := 𝓕.predictable) c u) := by
  have he : matrixAction T (coefficientMatrix b c L) u =
      fun a => ∑ j, inner ℝ (b a) (L (c j)) • u j :=
    funext (fun a => matrixAction_apply T (coefficientMatrix b c L) u a)
  rw [he]
  exact assemble_matrix (mΛ := 𝓕.predictable) c b L u

omit [IsProbabilityMeasure μ] in
theorem assemble_driftInput (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (u : τ → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T) :
    assemble (mΛ := 𝓕.predictable) b
      (driftInput T (coefficientMatrix b b A) (coefficientMatrix b c B) u X) =
      A.compLp (assemble (mΛ := 𝓕.predictable) b X) +
        B.compLp (assemble (mΛ := 𝓕.predictable) c u) := by
  rw [driftInput,assemble_add (mΛ := 𝓕.predictable),assemble_matrixAction,assemble_matrixAction]

omit [Fintype ι] [IsProbabilityMeasure μ] in
theorem assemble_noiseInput (T : ℝ≥0) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (u : τ → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T) (i : ι) :
    assemble (mΛ := 𝓕.predictable) b
      (noiseInput T (fun i => coefficientMatrix b b (C i)) (fun i => coefficientMatrix b c (D i)) u X i) =
      (C i).compLp (assemble (mΛ := 𝓕.predictable) b X) +
        (D i).compLp (assemble (mΛ := 𝓕.predictable) c u) := by
  rw [noiseInput,assemble_add (mΛ := 𝓕.predictable),assemble_matrixAction,assemble_matrixAction]
end Coefficients

section Existence
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι]
  (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

include hW hWc in
omit [CompleteSpace E] in
/-- The actual reconstructed terminal value is genuinely square integrable,
using the real drift-integral operator and actual per-time Itô L² operators. -/
theorem state_terminal_memLp (i₀ : ι) (T : ℝ≥0) (ξ : κ → Ω → ℝ)
    (hξ2 : ∀ a, MemLp (ξ a) 2 μ)
    (f : κ → H2 𝓕 μ T) (φ : ι → κ → H2 𝓕 μ T) :
    MemLp (state b hWm i₀ T ξ f φ T) 2 μ := by
  apply memLp_finsetSum Finset.univ
  intro a _
  apply (ContinuousLinearMap.toSpanSingleton ℝ (b a)).comp_memLp'
  have hg : MemLp (fun ω => ∫ s, f a (s,ω) ∂CommonItoCLM.timeMeasure_T T) 2 μ :=
    (memLp_congr_ae (BSDETerminal.terminal_ae 𝓕 T (f a))).mp (Lp.memLp _)
  have hi : MemLp (fun ω => ∑ i,
      CommonItoProcessGeneral.itoProcessCLM (hW i) T T (hWm i) (φ i a) ω) 2 μ :=
    memLp_finsetSum Finset.univ (fun i _ => Lp.memLp _)
  exact (memLp_congr_ae (CommonPicardRealization.realization_integral_identity hW hWm hWc
    i₀ T (ξ a) (f a) (fun i => φ i a) le_rfl)).mpr (((hξ2 a).add hg).add hi)

include c hWc in
/-- Genuine local existence for the original finite-dimensional coefficient
maps and an actual predictable L² control. The short-time premise is the
explicit previously proved Picard contraction rate, not a solution oracle. -/
theorem exists_section_solution (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    (hc : rate (𝓕 := 𝓕) (μ := μ) T (coefficientMatrix b b A)
      (fun i => coefficientMatrix b b (C i)) < 1) :
    ∃ (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Ω → E),
      SectionIntegralSolution b hW hWm T ξ (A.compLp X + B.compLp u)
        (fun i => (C i).compLp X + (D i).compLp u) X XT ∧
      MemLp XT 2 μ ∧ Nonempty (ContinuousRealization T ξ X XT) := by
  let a := coefficientMatrix b b A
  let β := coefficientMatrix b c B
  let γ := fun i => coefficientMatrix b b (C i)
  let δ := fun i => coefficientMatrix b c (D i)
  let η := fun a ω => inner ℝ (b a) (ξ ω)
  have hη (a : κ) : StronglyMeasurable[𝓕 0] (η a) :=
    (innerSL ℝ (b a)).continuous.comp_stronglyMeasurable hξ
  have hη2 (a : κ) : MemLp (η a) 2 μ := (innerSL ℝ (b a)).comp_memLp' hξ2
  let v := fun j => VectorItoProduct.coordinate c j u
  obtain ⟨Q,hQ,_⟩ := exists_unique_initial_fixedPoint hW hWm hWc i₀ T a β γ δ η hη hη2 v hc
  let f := driftInput T a β v Q
  let φ := noiseInput T γ δ v Q
  have hrep := fixedPoint_state_ae hW hWm hWc i₀ T a β γ δ η hη hη2 v Q hQ
  have hs := section_solution b hW hWm hWc i₀ T η f φ Q hrep
  have hr := continuousRealization b hW hWm hWc i₀ T η f φ Q hrep
  have hηeq : (fun ω => ∑ a, η a ω • b a) = ξ := funext (fun ω => b.sum_repr' (ξ ω))
  have hv : assemble (mΛ := 𝓕.predictable) c v = u := assemble_coordinates (mΛ := 𝓕.predictable) c u
  have hf : assemble (mΛ := 𝓕.predictable) b f =
      A.compLp (assemble (mΛ := 𝓕.predictable) b Q) + B.compLp u := by
    rw [show f = driftInput T (coefficientMatrix b b A) (coefficientMatrix b c B) v Q from rfl,
      assemble_driftInput,hv]
  have hφ : (fun i => assemble (mΛ := 𝓕.predictable) b (φ i)) =
      fun i => (C i).compLp (assemble (mΛ := 𝓕.predictable) b Q) + (D i).compLp u := by
    funext i
    rw [show φ i = noiseInput T (fun i => coefficientMatrix b b (C i))
      (fun i => coefficientMatrix b c (D i)) v Q i from rfl,assemble_noiseInput,hv]
  rw [hηeq,hf,hφ] at hs
  rw [hηeq] at hr
  exact ⟨assemble (mΛ := 𝓕.predictable) b Q,state b hWm i₀ T η f φ T,hs,
    state_terminal_memLp b hW hWm hWc i₀ T η hη2 f φ,⟨hr⟩⟩
end Existence

#print axioms exists_section_solution
end LinearStochastic.HilbertLocalSolution
