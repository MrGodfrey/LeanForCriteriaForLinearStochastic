module

public import LinearStochastic.LpOrthonormalCoordinates
public import LinearStochastic.SectionLinearDuality
public import LinearStochastic.CommonPicardRealization

@[expose] public section

/-! Exact reconstruction of the actual coordinate Lebesgue/Itô integrals
into the Hilbert-valued integral-solution interface. -/
noncomputable section
namespace LinearStochastic.CoordinateIntegralReconstruction
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonVectorPicard CommonPicardRealization
open LpOrthonormalCoordinates VectorItoProduct LinearDuality

variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

omit hW hWm hWc [CompleteSpace E] in
theorem assemble_real_ae (T : ℝ≥0) (f : κ → H2 𝓕 μ T) :
    (fun z : ℝ × Ω => assemble (mΛ := 𝓕.predictable) b f (z.1.toNNReal,z.2)) =ᵐ[
      (volume.restrict (Ioc 0 (T : ℝ))).prod μ]
      fun z => ∑ a, f a (z.1.toNNReal,z.2) • b a := by
  have he := ae_of_ae_trim 𝓕.predictable_le_prod (assemble_ae (mΛ := 𝓕.predictable) b f)
  exact ((RealTimeBridge.toNNReal_measurePreserving T).prod
    (MeasurePreserving.id μ)).quasiMeasurePreserving.ae_eq_comp he

omit hW hWm hWc in
/-- Actual Bochner integration of reconstructed L² coordinates commutes with
the finite basis sum, with path integrability obtained from Fubini. -/
theorem primitive_assemble_ae (T : ℝ≥0) (s : ℝ) (hs : s ≤ T) (f : κ → H2 𝓕 μ T) :
    (fun ω => ∫ t in Ioc 0 s, assemble (mΛ := 𝓕.predictable) b f (t.toNNReal,ω)) =ᵐ[μ]
      fun ω => ∑ a, (∫ t in Ioc 0 s, f a (t.toNNReal,ω)) • b a := by
  have he := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae (assemble_real_ae b T f))
  have hi : ∀ᵐ ω ∂μ, ∀ a, IntegrableOn (fun t : ℝ => f a (t.toNNReal,ω)) (Ioc 0 (T : ℝ)) := by
    rw [ae_all_iff]
    exact fun a => ((RealTimeBridge.predictable_memLp_real_extension T μ 𝓕 (f a)).integrable one_le_two).prod_left_ae
  filter_upwards [he,hi] with ω he hi
  change (fun t => assemble (mΛ := 𝓕.predictable) b f (t.toNNReal,ω)) =ᵐ[
    volume.restrict (Ioc 0 (T : ℝ))] fun t => ∑ a, f a (t.toNNReal,ω) • b a at he
  have hsub : Ioc (0 : ℝ) s ⊆ Ioc 0 (T : ℝ) := Ioc_subset_Ioc_right hs
  rw [integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hsub he)]
  rw [integral_finsetSum Finset.univ]
  · exact Finset.sum_congr rfl (fun a _ =>
      (ContinuousLinearMap.toSpanSingleton ℝ (b a)).integral_comp_comm ((hi a).mono_set hsub))
  · intro a _
    exact ((ContinuousLinearMap.toSpanSingleton ℝ (b a)).integrable_comp ((hi a).mono_set hsub))

/-- The genuine coordinate continuous versions reconstructed in the state
Hilbert space. -/
def state (i₀ : ι) (T : ℝ≥0) (ξ : κ → Ω → ℝ)
    (f : κ → H2 𝓕 μ T) (φ : ι → κ → H2 𝓕 μ T) (t : ℝ≥0) (ω : Ω) : E :=
  ∑ a, realization hWm i₀ T (ξ a) (f a) (fun i => φ i a) t ω • b a

include hWc in
/-- Every fixed-time coordinate realization solves exactly the reconstructed
vector Lebesgue/constructed-Itô equation. -/
theorem state_integral_ae (i₀ : ι) (T t : ℝ≥0) (ht : t ≤ T) (ξ : κ → Ω → ℝ)
    (f : κ → H2 𝓕 μ T) (φ : ι → κ → H2 𝓕 μ T) :
    state b hWm i₀ T ξ f φ t =ᵐ[μ]
      integralState b hW hWm T (fun ω => ∑ a, ξ a ω • b a)
        (assemble (mΛ := 𝓕.predictable) b f)
        (fun i => assemble (mΛ := 𝓕.predictable) b (φ i)) (t : ℝ) := by
  have hr : ∀ᵐ ω ∂μ, ∀ a,
      realization hWm i₀ T (ξ a) (f a) (fun i => φ i a) t ω =
        ξ a ω + (∫ s in Ioc 0 (t : ℝ), f a (s.toNNReal,ω)) +
          ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i) (φ i a) ω := by
    rw [ae_all_iff]
    intro a
    filter_upwards [realization_integral_identity hW hWm hWc i₀ T (ξ a) (f a)
      (fun i => φ i a) ht] with ω hω
    rw [RealTimeBridge.integral_real_extension t (fun s => f a (s,ω))]
    exact hω
  have hi : ∀ᵐ ω ∂μ, ∀ a i,
      CommonItoMartingaleVersion.integralProcess (hW i) T (hWm i) (φ i a) t ω =
        CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i) (φ i a) ω := by
    simp only [ae_all_iff]
    exact fun a i => CommonItoMartingaleVersion.integralProcess_ae_eq (hW i) T t (hWm i) (φ i a)
  filter_upwards [hr,hi,primitive_assemble_ae b T t (by exact_mod_cast ht) f] with ω hr hi hd
  simp only [state,hr,integralState,hd,Real.toNNReal_coe,vectorProcess,coordinate_assemble,
    ItoExpectedProduct.sumProcess,hi,add_smul,Finset.sum_add_distrib]
  abel

#print axioms state_integral_ae
end LinearStochastic.CoordinateIntegralReconstruction
