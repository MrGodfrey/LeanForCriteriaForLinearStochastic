module

public import LinearStochastic.HilbertLocalSolution
public import LinearStochastic.SectionSolutionMap

@[expose] public section

/-! Exact scalar coordinate consequences of any actual Hilbert section
solution. In particular, no joint measurability of the raw Itô version is
assumed when extracting real-clock almost-everywhere scalar equations. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.HilbertSectionCoordinates
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonVectorPicard CommonLocalSolution LpOrthonormalCoordinates
open VectorItoProduct LinearDuality SectionLinearDuality HilbertLocalSolution

variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Each orthonormal coordinate of the actual vector integral is the literal
scalar drift plus the sum of the constructed scalar Itô integrals. -/
theorem integral_coordinate_ae (T : ℝ≥0) (s : ℝ) (hs : s ≤ T) (ξ : Ω → E)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) (a : κ) :
    (fun ω => inner ℝ (b a) (integralState b hW hWm T ξ f φ s ω)) =ᵐ[μ]
      fun ω => inner ℝ (b a) (ξ ω) + (∫ t in Ioc 0 s, coordinate b a f (t.toNNReal,ω)) +
        ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T s.toNNReal (hWm i) (coordinate b a (φ i)) ω := by
  have hi : ∀ᵐ ω ∂μ, ∀ i, CommonItoMartingaleVersion.integralProcess (hW i) T (hWm i)
      (coordinate b a (φ i)) s.toNNReal ω =
      CommonItoProcessGeneral.itoProcessCLM (hW i) T s.toNNReal (hWm i) (coordinate b a (φ i)) ω := by
    rw [ae_all_iff]
    exact fun i => CommonItoMartingaleVersion.integralProcess_ae_eq (hW i) T s.toNNReal (hWm i) _
  filter_upwards [SectionSolutionMap.primitive_comp_ae T s hs (innerSL ℝ (b a)) f,hi] with ω hd hi
  change (∫ t in Ioc 0 s, coordinate b a f (t.toNNReal,ω)) =
    inner ℝ (b a) (∫ t in Ioc 0 s, f (t.toNNReal,ω)) at hd
  simp only [integralState,inner_add_right,←hd,vectorProcess,b.orthonormal.inner_right_fintype,
    ItoExpectedProduct.sumProcess]
  simp only [hi]
  abel

/-- The true sections of any vector integral solution give true sections of
each scalar integral equation. -/
theorem sections_coordinates (T : ℝ≥0) (ξ XT : Ω → E)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT) (a : κ) :
    ∀ᵐ s ∂volume.restrict (Ioc 0 (T:ℝ)),
      (fun ω => coordinate b a X (s.toNNReal,ω)) =ᵐ[μ]
        fun ω => inner ℝ (b a) (ξ ω) + (∫ t in Ioc 0 s, coordinate b a f (t.toNNReal,ω)) +
          ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T s.toNNReal (hWm i) (coordinate b a (φ i)) ω := by
  filter_upwards [hX.sections,Measure.ae_ae_of_ae_prod
    (SectionSolutionMap.real_compLp_ae T (innerSL ℝ (b a)) X),ae_restrict_mem measurableSet_Ioc]
    with s hs hc hsm
  exact Filter.EventuallyEq.trans hc (Filter.EventuallyEq.trans (hs.fun_comp (innerSL ℝ (b a)))
    (integral_coordinate_ae b hW hWm T s hsm.2 ξ f φ a))

/-- The separately supplied terminal endpoint is also the genuine scalar
integral endpoint, not merely a time-almost-everywhere value. -/
theorem terminal_coordinates (T : ℝ≥0) (ξ XT : Ω → E)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT) (a : κ) :
    (fun ω => inner ℝ (b a) (XT ω)) =ᵐ[μ]
      fun ω => inner ℝ (b a) (ξ ω) + (∫ t in Ioc 0 (T:ℝ), coordinate b a f (t.toNNReal,ω)) +
        ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T T (hWm i) (coordinate b a (φ i)) ω := by
  have he := integral_coordinate_ae b hW hWm T T le_rfl ξ f φ a
  rw [Real.toNNReal_coe] at he
  exact Filter.EventuallyEq.trans (hX.terminal.fun_comp (innerSL ℝ (b a))) he

omit hW hWm [CompleteSpace E] [IsProbabilityMeasure μ] in
/-- The scalar drift obtained by inner products is precisely the actual
matrix driftInput for the two chosen orthonormal bases. -/
theorem drift_coordinates (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (a : κ) :
    coordinate b a (A.compLp X+B.compLp u) = driftInput T (coefficientMatrix b b A)
      (coefficientMatrix b c B) (fun j => coordinate c j u) (fun j => coordinate b j X) a := by
  have he := assemble_driftInput b c T A B (fun j => coordinate c j u) (fun j => coordinate b j X)
  rw [assemble_coordinates (mΛ:=𝓕.predictable),assemble_coordinates (mΛ:=𝓕.predictable)] at he
  rw [←he,coordinate_assemble (mΛ:=𝓕.predictable)]

omit hW hWm [CompleteSpace E] [IsProbabilityMeasure μ] [Fintype ι] in
/-- Each scalar diffusion uses exactly the original C_i and D_i matrices. -/
theorem noise_coordinates (T : ℝ≥0) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (a : κ) (i : ι) :
    coordinate b a ((C i).compLp X+(D i).compLp u) = noiseInput T
      (fun i => coefficientMatrix b b (C i)) (fun i => coefficientMatrix b c (D i))
      (fun j => coordinate c j u) (fun j => coordinate b j X) i a := by
  have he := assemble_noiseInput b c T C D (fun j => coordinate c j u) (fun j => coordinate b j X) i
  rw [assemble_coordinates (mΛ:=𝓕.predictable),assemble_coordinates (mΛ:=𝓕.predictable)] at he
  rw [←he,coordinate_assemble (mΛ:=𝓕.predictable)]

end LinearStochastic.HilbertSectionCoordinates
