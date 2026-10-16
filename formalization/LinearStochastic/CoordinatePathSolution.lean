import LinearStochastic.CoordinateIntegralReconstruction
import LinearStochastic.ContinuousRealization
import LinearStochastic.CommonSolutionData

/-! Any actual coordinate integral solution, including deterministic-time
pasted global solutions, reconstructs into the exact Hilbert integral equation. -/
noncomputable section
namespace LinearStochastic.CoordinatePathSolution
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonVectorPicard LpOrthonormalCoordinates
open CoordinateIntegralReconstruction LinearDuality SectionLinearDuality VectorItoProduct

variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Literal finite orthonormal reconstruction of actual coordinate paths. -/
def reconstruct (R : κ → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : E := ∑ a, R a t ω • b a

omit hW hWm [CompleteSpace E] in
theorem space_ae (T : ℝ≥0) (X : κ → H2 𝓕 μ T) (R : κ → ℝ≥0 → Ω → ℝ)
    (hX : ∀ a, X a =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry (R a)) :
    (fun z : ℝ × Ω => assemble (mΛ:=𝓕.predictable) b X (z.1.toNNReal,z.2)) =ᵐ[
      (volume.restrict (Ioc 0 (T:ℝ))).prod μ]
      fun z => reconstruct b R z.1.toNNReal z.2 := by
  have hall : ∀ᵐ z ∂(CommonItoCLM.timeMeasure_T T).prod μ, ∀ a, X a z = R a z.1 z.2 := by
    rw [ae_all_iff]
    exact hX
  have hr := ((RealTimeBridge.toNNReal_measurePreserving T).prod (MeasurePreserving.id μ)).quasiMeasurePreserving.ae hall
  filter_upwards [assemble_real_ae b T X,hr] with z ha hr
  rw [ha]
  exact Finset.sum_congr rfl (fun a _ => congrArg (fun q : ℝ => q • b a) (hr a))

/-- Each real coordinate equation is transported to the actual vector Itô
integral, with no common null set over uncountably many times assumed. -/
theorem integral_ae (T t : ℝ≥0) (ht : t ≤ T) (ξ : κ → Ω → ℝ)
    (f : κ → H2 𝓕 μ T) (φ : ι → κ → H2 𝓕 μ T) (R : κ → ℝ≥0 → Ω → ℝ)
    (hR : ∀ a, CommonIntegralPaste.IntegralEquation hW hWm T (ξ a) (f a) (fun i => φ i a) (R a)) :
    reconstruct b R t =ᵐ[μ] integralState b hW hWm T (fun ω => ∑ a, ξ a ω • b a)
      (assemble (mΛ:=𝓕.predictable) b f) (fun i => assemble (mΛ:=𝓕.predictable) b (φ i)) (t:ℝ) := by
  have hr : ∀ᵐ ω ∂μ, ∀ a, R a t ω = ξ a ω + (∫ s in Ioc 0 (t:ℝ), f a (s.toNNReal,ω)) +
      ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i) (φ i a) ω := by
    rw [ae_all_iff]
    intro a
    filter_upwards [hR a t ht] with ω hω
    rw [RealTimeBridge.integral_real_extension t (fun s => f a (s,ω))]
    exact hω
  have hi : ∀ᵐ ω ∂μ, ∀ a i, CommonItoMartingaleVersion.integralProcess (hW i) T (hWm i) (φ i a) t ω =
      CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i) (φ i a) ω := by
    simp only [ae_all_iff]
    exact fun a i => CommonItoMartingaleVersion.integralProcess_ae_eq (hW i) T t (hWm i) (φ i a)
  filter_upwards [hr,hi,primitive_assemble_ae b T t (by exact_mod_cast ht) f] with ω hr hi hd
  simp only [reconstruct,hr,integralState,hd,Real.toNNReal_coe,vectorProcess,coordinate_assemble,
    ItoExpectedProduct.sumProcess,hi,add_smul,Finset.sum_add_distrib]
  abel

theorem section_solution (T : ℝ≥0) (ξ : κ → Ω → ℝ)
    (f : κ → H2 𝓕 μ T) (φ : ι → κ → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (R : κ → ℝ≥0 → Ω → ℝ)
    (hX : ∀ a, X a =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry (R a))
    (hR : ∀ a, CommonIntegralPaste.IntegralEquation hW hWm T (ξ a) (f a) (fun i => φ i a) (R a)) :
    SectionIntegralSolution b hW hWm T (fun ω => ∑ a, ξ a ω • b a)
      (assemble (mΛ:=𝓕.predictable) b f) (fun i => assemble (mΛ:=𝓕.predictable) b (φ i))
      (assemble (mΛ:=𝓕.predictable) b X) (reconstruct b R T) := by
  constructor
  · filter_upwards [Measure.ae_ae_of_ae_prod (space_ae b T X R hX),ae_restrict_mem measurableSet_Ioc]
      with s hs hsm
    have he := integral_ae b hW hWm T s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hsm.2) ξ f φ R hR
    rw [Real.coe_toNNReal s hsm.1.le] at he
    exact Filter.EventuallyEq.trans hs he
  · exact integral_ae b hW hWm T T le_rfl ξ f φ R hR

omit hW hWm in
/-- The genuine continuous coordinate paths provide a product-measure version
and both endpoint values of the Hilbert state. -/
def continuousRealization (T : ℝ≥0) (ξ : κ → Ω → ℝ) (X : κ → H2 𝓕 μ T)
    (R : κ → ℝ≥0 → Ω → ℝ)
    (hX : ∀ a, X a =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry (R a))
    (hc : ∀ a, ∀ᵐ ω ∂μ, ContinuousOn (fun t => R a t ω) (Iic T))
    (hi : ∀ a, R a 0 =ᵐ[μ] ξ a) :
    ContinuousRealization T (fun ω => ∑ a, ξ a ω • b a) (assemble (mΛ:=𝓕.predictable) b X)
      (reconstruct b R T) where
  path s ω := reconstruct b R s.toNNReal ω
  continuous := by
    have hall : ∀ᵐ ω ∂μ, ∀ a, ContinuousOn (fun t => R a t ω) (Iic T) := by
      rw [ae_all_iff]; exact hc
    filter_upwards [hall] with ω hω
    apply continuousOn_finsetSum
    intro a _
    apply ((hω a).comp continuous_real_toNNReal.continuousOn ?_).smul continuousOn_const
    exact fun s hs => Real.toNNReal_le_iff_le_coe.mpr hs.2
  spacetime := (space_ae b T X R hX).symm
  initial := by
    have hall : ∀ᵐ ω ∂μ, ∀ a, R a 0 ω = ξ a ω := by rw [ae_all_iff]; exact hi
    filter_upwards [hall] with ω hω
    simp only [reconstruct,Real.toNNReal_zero,hω]
  terminal := by simp only [Real.toNNReal_coe]; rfl

omit hW hWm [CompleteSpace E] in
/-- Finite reconstruction preserves true progressiveness in the same filtration. -/
theorem reconstruct_progressive (R : κ → ℝ≥0 → Ω → ℝ)
    (hR : ∀ a, IsStronglyProgressive 𝓕 (R a)) :
    IsStronglyProgressive 𝓕 (reconstruct b R) := by
  intro t
  exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun a _ => (hR a t).smul_const (b a))

omit hW hWm [CompleteSpace E] [IsProbabilityMeasure μ] in
/-- The actual Hilbert path norm is S² when all its actual coordinates are. -/
theorem reconstruct_S2 (T : ℝ≥0) (R : κ → ℝ≥0 → Ω → ℝ)
    (hR : ∀ a, IsStronglyProgressive 𝓕 (R a))
    (hc : ∀ a, ∀ᵐ ω ∂μ, ContinuousOn (fun t => R a t ω) (Iic T))
    (h2 : ∀ a, MemLp (ContinuousDoobL2.pathSup (R a) T) 2 μ) :
    MemLp (ContinuousDoobL2.pathSup (reconstruct b R) T) 2 μ :=
  CommonStateS2.vector_reconstruct_S2 b T R (fun a => (hR a).stronglyAdapted) hc h2

end LinearStochastic.CoordinatePathSolution
