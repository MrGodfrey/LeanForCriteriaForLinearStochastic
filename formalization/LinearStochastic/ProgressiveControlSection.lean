module

public import LinearStochastic.CommonProcessSpace
public import LinearStochastic.SectionLinearDuality
public import LinearStochastic.SectionSolutionLinearity

@[expose] public section

/-! Ordinary progressive controls and raw continuous S² paths are connected
in both directions to the actual predictable L² section interface. Every
coefficient class is proved to represent the literal raw coefficient process. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.ProgressiveControlSection
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace
open CommonItoMultichannel VectorItoProduct LinearDuality SectionLinearDuality
variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

omit hW hWm b [Fintype κ] [Fintype ι] in
/-- Any ordinary progressive L² control and actual progressive S² state have
genuine predictable representatives with the same ambient product-measure values. -/
theorem representatives (T : ℝ≥0) (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
    (hv : IsStronglyProgressive 𝓕 v) (hv2 : MemLp (Function.uncurry v) 2 ((CommonItoCLM.timeMeasure_T T).prod μ))
    (hR : IsStronglyProgressive 𝓕 R) (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (hR2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ) :
    ∃ (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)),
      (u : ℝ≥0 × Ω → U) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry v ∧
      (X : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R := by
  obtain ⟨u,hu⟩ := ProgressivePredictable.exists_predictable_Lp μ hv T 2 hv2
  obtain ⟨X,hX⟩ := ProgressivePredictable.exists_predictable_Lp μ hR T 2
    (CommonProcessSpace.spacetime_memLp_of_s2 hR T hc hR2)
  exact ⟨u,X,hu,hX⟩

omit hW hWm b [Fintype κ] [Fintype ι] [CompleteSpace E] [CompleteSpace U] [IsProbabilityMeasure μ] in
/-- The actual coefficient class is the literal original raw coefficient
process in product measure, for the drift and separately for every diffusion. -/
theorem coefficient_ae (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hu : (u : ℝ≥0 × Ω → U) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry v)
    (hX : (X : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R) :
    ((A.compLp X+B.compLp u : Lp E 2 (spacetimeMeasure 𝓕 μ T)) : ℝ≥0 × Ω → E)
      =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] fun z => A (R z.1 z.2)+B (v z.1 z.2) := by
  filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod (Lp.coeFn_add (A.compLp X) (B.compLp u)),
    ae_of_ae_trim 𝓕.predictable_le_prod (A.coeFn_compLp X),
    ae_of_ae_trim 𝓕.predictable_le_prod (B.coeFn_compLp u),hu,hX] with z ha hA hB hu hX
  rw [ha,Pi.add_apply,hA,hB,hu,hX]
  rfl

omit hW hWm b [Fintype κ] [Fintype ι] [CompleteSpace E] [CompleteSpace U] in
/-- Pathwise drift integrals agree for every prescribed time, by actual Fubini
and real-clock measure preservation. -/
theorem primitive_ae (T : ℝ≥0) (s : ℝ) (hs : s ≤ T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hu : (u : ℝ≥0 × Ω → U) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry v)
    (hX : (X : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R) :
    (fun ω => ∫ t in Ioc 0 s, (A.compLp X+B.compLp u) (t.toNNReal,ω)) =ᵐ[μ]
      fun ω => ∫ t in Ioc 0 s, A (R t.toNNReal ω)+B (v t.toNNReal ω) := by
  have he := ((RealTimeBridge.toNNReal_measurePreserving T).prod (MeasurePreserving.id μ)).quasiMeasurePreserving.ae_eq_comp
    (coefficient_ae T A B v R u X hu hX)
  have hf := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae he)
  filter_upwards [hf] with ω hω
  exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right hs) hω)

/-- A raw controlled equation with ordinary progressive control v and actual
state path R. The representative conditions identify each Itô integrand with
C_i R + D_i v by coefficient_ae; they are not new control assumptions. -/
structure RawSolution (T : ℝ≥0) (ξ : Ω → E)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) : Prop where
  control_progressive : IsStronglyProgressive 𝓕 v
  control_memLp : MemLp (Function.uncurry v) 2 ((CommonItoCLM.timeMeasure_T T).prod μ)
  progressive : IsStronglyProgressive 𝓕 R
  continuous : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T)
  squareSup : MemLp (ContinuousDoobL2.pathSup R T) 2 μ
  control_rep : (u : ℝ≥0 × Ω → U) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry v
  state_rep : (X : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R
  equation : ∀ t, t ≤ T → R t =ᵐ[μ] fun ω =>
    (∫ s in Ioc 0 (t:ℝ), A (R s.toNNReal ω)+B (v s.toNNReal ω)) +
      (ξ ω+vectorProcess b hW hWm T (fun i => (C i).compLp X+(D i).compLp u) t ω)

omit [CompleteSpace E] [CompleteSpace U] in
/-- Every raw ordinary-progressive S² integral solution supplies the section
interface, with its actual terminal value retained exactly. -/
theorem RawSolution.to_section (T : ℝ≥0) (ξ : Ω → E)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (q : RawSolution b hW hWm T ξ A B C D v R u X) :
    SectionIntegralSolution b hW hWm T ξ (A.compLp X+B.compLp u)
      (fun i => (C i).compLp X+(D i).compLp u) X (R T) := by
  have eq (t : ℝ≥0) (ht : t ≤ T) : R t =ᵐ[μ] integralState b hW hWm T ξ
      (A.compLp X+B.compLp u) (fun i => (C i).compLp X+(D i).compLp u) (t:ℝ) := by
    filter_upwards [q.equation t ht,primitive_ae T t (by exact_mod_cast ht) A B v R u X q.control_rep q.state_rep]
      with ω he hd
    simpa only [integralState,Real.toNNReal_coe,hd] using he
  constructor
  · have hr := ((RealTimeBridge.toNNReal_measurePreserving T).prod (MeasurePreserving.id μ)).quasiMeasurePreserving.ae_eq_comp q.state_rep
    filter_upwards [Measure.ae_ae_of_ae_prod hr,ae_restrict_mem measurableSet_Ioc] with s hs hsm
    have he := eq s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hsm.2)
    rw [Real.coe_toNNReal s hsm.1.le] at he
    exact Filter.EventuallyEq.trans hs he
  · exact eq T le_rfl


omit [CompleteSpace E] [CompleteSpace U] in
/-- A true class-based path equation also gives the raw equation for the
ordinary progressive representative of that very same control. -/
theorem RawSolution.of_class_path (T : ℝ≥0) (ξ : Ω → E)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (R : ℝ≥0 → Ω → E) (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hp : IsStronglyProgressive 𝓕 R) (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (h2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ)
    (hX : (X : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R)
    (he : ∀ t, t ≤ T → R t =ᵐ[μ] integralState b hW hWm T ξ (A.compLp X+B.compLp u)
      (fun i => (C i).compLp X+(D i).compLp u) (t:ℝ)) :
    RawSolution b hW hWm T ξ A B C D (fun t ω => u (t,ω)) R u X := by
  have hu : IsStronglyPredictable 𝓕 (fun t ω => u (t,ω)) := Lp.stronglyMeasurable u
  refine ⟨hu.isStronglyProgressive,memLp_of_memLp_trim 𝓕.predictable_le_prod (Lp.memLp u),
    hp,hc,h2,Filter.EventuallyEq.rfl,hX,?_⟩
  intro t ht
  filter_upwards [he t ht,primitive_ae T t (by exact_mod_cast ht) A B
    (fun s ω => u (s,ω)) R u X Filter.EventuallyEq.rfl hX] with ω he hd
  simpa only [integralState,Real.toNNReal_coe,hd] using he

omit hW hWm b [Fintype κ] [Fintype ι] in
/-- For the paper's finite-dimensional Borel spaces the ordinary progressive
hypothesis yields all representatives; no strong-progressive restriction is
imposed on admissible controls or state paths. -/
theorem representatives_of_progressive [MeasurableSpace E] [MeasurableSpace U]
    [SecondCountableTopology E] [SecondCountableTopology U]
    [OpensMeasurableSpace E] [OpensMeasurableSpace U]
    (T : ℝ≥0) (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
    (hv : IsProgressive 𝓕 v) (hv2 : MemLp (Function.uncurry v) 2 ((CommonItoCLM.timeMeasure_T T).prod μ))
    (hR : IsProgressive 𝓕 R) (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (hR2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ) :
    ∃ (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)),
      (u : ℝ≥0 × Ω → U) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry v ∧
      (X : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R :=
  representatives T v R hv.isStronglyProgressive hv2 hR.isStronglyProgressive hc hR2

end LinearStochastic.ProgressiveControlSection
