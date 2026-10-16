import LinearStochastic.CoordinateIntegralReconstruction
import LinearStochastic.ContinuousRealization
import LinearStochastic.CommonLocalSolution

/-! Actual continuous coordinate realizations, including the constructed
Picard solutions, supply the Hilbert-valued sectionwise integral interface. -/
noncomputable section
namespace LinearStochastic.CoordinateSectionSolution
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonVectorPicard CommonPicardRealization CommonLocalSolution
open LpOrthonormalCoordinates CoordinateIntegralReconstruction LinearDuality SectionLinearDuality

variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

omit hW hWc [CompleteSpace E] in
theorem state_space_ae (i₀ : ι) (T : ℝ≥0) (ξ : κ → Ω → ℝ)
    (f : κ → H2 𝓕 μ T) (φ : ι → κ → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (hX : ∀ a, X a =ᵐ[spacetimeMeasure 𝓕 μ T]
      Function.uncurry (realization hWm i₀ T (ξ a) (f a) (fun i => φ i a))) :
    (fun z : ℝ × Ω => assemble (mΛ := 𝓕.predictable) b X (z.1.toNNReal,z.2)) =ᵐ[
      (volume.restrict (Ioc 0 (T : ℝ))).prod μ]
      fun z => state b hWm i₀ T ξ f φ z.1.toNNReal z.2 := by
  have hc : ∀ᵐ z ∂spacetimeMeasure 𝓕 μ T, ∀ a,
      X a z = realization hWm i₀ T (ξ a) (f a) (fun i => φ i a) z.1 z.2 := by
    rw [ae_all_iff]
    exact hX
  have hr := ((RealTimeBridge.toNNReal_measurePreserving T).prod (MeasurePreserving.id μ)).quasiMeasurePreserving.ae
    (ae_of_ae_trim 𝓕.predictable_le_prod hc)
  filter_upwards [assemble_real_ae b T X,hr] with z he hr
  rw [he]
  exact Finset.sum_congr rfl (fun a _ => congrArg (fun q : ℝ => q • b a) (hr a))

include hW hWc in
omit [CompleteSpace E] in
theorem state_continuous (i₀ : ι) (T : ℝ≥0) (ξ : κ → Ω → ℝ)
    (f : κ → H2 𝓕 μ T) (φ : ι → κ → H2 𝓕 μ T) :
    ∀ᵐ ω ∂μ, ContinuousOn (fun s : ℝ => state b hWm i₀ T ξ f φ s.toNNReal ω) (Icc 0 (T : ℝ)) := by
  have hc : ∀ᵐ ω ∂μ, ∀ a, ContinuousOn
      (fun t => realization hWm i₀ T (ξ a) (f a) (fun i => φ i a) t ω) (Icc 0 T) := by
    rw [ae_all_iff]
    exact fun a => realization_continuousOn hW hWm hWc i₀ T (ξ a) (f a) (fun i => φ i a)
  filter_upwards [hc] with ω hc
  apply continuousOn_finsetSum
  intro a _
  apply ((hc a).comp continuous_real_toNNReal.continuousOn ?_).smul continuousOn_const
  intro s hs
  exact ⟨bot_le,Real.toNNReal_le_iff_le_coe.mpr hs.2⟩

include hW hWc in
omit [CompleteSpace E] in
theorem state_initial_ae (i₀ : ι) (T : ℝ≥0) (ξ : κ → Ω → ℝ)
    (f : κ → H2 𝓕 μ T) (φ : ι → κ → H2 𝓕 μ T) :
    state b hWm i₀ T ξ f φ 0 =ᵐ[μ] fun ω => ∑ a, ξ a ω • b a := by
  have hc : ∀ᵐ ω ∂μ, ∀ a,
      realization hWm i₀ T (ξ a) (f a) (fun i => φ i a) 0 ω = ξ a ω := by
    rw [ae_all_iff]
    exact fun a => realization_initial hW hWm hWc i₀ T (ξ a) (f a) (fun i => φ i a)
  filter_upwards [hc] with ω hc
  simp only [state,hc]

include hW hWc in
/-- Reconstruct the genuine continuous version, with its actual initial and
terminal values and a proved product-measure equality to the L² state. -/
def continuousRealization (i₀ : ι) (T : ℝ≥0) (ξ : κ → Ω → ℝ)
    (f : κ → H2 𝓕 μ T) (φ : ι → κ → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (hX : ∀ a, X a =ᵐ[spacetimeMeasure 𝓕 μ T]
      Function.uncurry (realization hWm i₀ T (ξ a) (f a) (fun i => φ i a))) :
    ContinuousRealization T (fun ω => ∑ a, ξ a ω • b a) (assemble (mΛ := 𝓕.predictable) b X)
      (state b hWm i₀ T ξ f φ T) where
  path s ω := state b hWm i₀ T ξ f φ s.toNNReal ω
  continuous := state_continuous b hW hWm hWc i₀ T ξ f φ
  spacetime := (state_space_ae b hWm i₀ T ξ f φ X hX).symm
  initial := by simpa only [Real.toNNReal_zero] using (state_initial_ae b hW hWm hWc i₀ T ξ f φ).symm
  terminal := by simp only [Real.toNNReal_coe]; rfl

include hWc in
/-- The reconstructed coordinate integral solution meets the actual vector
sectionwise equation, without requiring the raw Itô version to be jointly measurable. -/
theorem section_solution (i₀ : ι) (T : ℝ≥0) (ξ : κ → Ω → ℝ)
    (f : κ → H2 𝓕 μ T) (φ : ι → κ → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T)
    (hX : ∀ a, X a =ᵐ[spacetimeMeasure 𝓕 μ T]
      Function.uncurry (realization hWm i₀ T (ξ a) (f a) (fun i => φ i a))) :
    SectionIntegralSolution b hW hWm T (fun ω => ∑ a, ξ a ω • b a)
      (assemble (mΛ := 𝓕.predictable) b f) (fun i => assemble (mΛ := 𝓕.predictable) b (φ i))
      (assemble (mΛ := 𝓕.predictable) b X) (state b hWm i₀ T ξ f φ T) := by
  constructor
  · filter_upwards [Measure.ae_ae_of_ae_prod (state_space_ae b hWm i₀ T ξ f φ X hX),
      ae_restrict_mem measurableSet_Ioc] with s hs hsm
    have ht : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hsm.2
    have he := state_integral_ae b hW hWm hWc i₀ T s.toNNReal ht ξ f φ
    rw [Real.coe_toNNReal s hsm.1.le] at he
    apply Filter.EventuallyEq.trans ?_ he
    exact hs
  · exact state_integral_ae b hW hWm hWc i₀ T T le_rfl ξ f φ

#print axioms section_solution
end LinearStochastic.CoordinateSectionSolution
