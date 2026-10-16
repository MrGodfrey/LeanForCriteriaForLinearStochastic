import LinearStochastic.ProcessQuadraticInner
import LinearStochastic.LpLyapunovEstimate

/-! The actual expected quadratic generator: continuity from S² domination,
its pointwise Lyapunov bound, and the exact time-integral decomposition. -/
noncomputable section
namespace LinearStochastic.ExpectedQuadraticGenerator
open MeasureTheory Set
open scoped NNReal InnerProductSpace BigOperators
variable {Ω E ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

def generator (R : ℝ≥0 → Ω → E) (H A : E →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (t : ℝ≥0) : ℝ :=
  (∑ i, ∫ ω, inner ℝ (C i (R t ω)) (H (C i (R t ω))) ∂μ) +
    2 * ∫ ω, inner ℝ (A (R t ω)) (H (R t ω)) ∂μ

theorem continuous_clamped (T : ℝ≥0) (R : ℝ≥0 → Ω → E)
    (hm : ∀ t, AEStronglyMeasurable (R t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (h2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ)
    (H A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) :
    Continuous (fun s : ℝ => generator (μ:=μ) R H A C (min s.toNNReal T)) := by
  have hd (i : ι) := ProcessQuadraticInner.continuous_expected_product_clamped T R hm hc h2
    (C i) (H.comp (C i))
  have ha := ProcessQuadraticInner.continuous_expected_product_clamped T R hm hc h2 A H
  exact (continuous_finsetSum _ (fun i _ => hd i)).add (continuous_const.mul ha)

omit [IsProbabilityMeasure μ] in
theorem generator_le (R : ℝ≥0 → Ω → E) (H A : E →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (ρ : ℝ)
    (hq : ∀ x, (∑ i, inner ℝ (C i x) (H (C i x))) +
      2 * inner ℝ (A x) (H x) ≤ -ρ * inner ℝ x (H x))
    (t : ℝ≥0) (ht : MemLp (R t) 2 μ) :
    generator (μ:=μ) R H A C t ≤ -ρ * ∫ ω, inner ℝ (R t ω) (H (R t ω)) ∂μ := by
  have hd (i) : Integrable (fun ω => inner ℝ (C i (R t ω)) (H (C i (R t ω)))) μ :=
    DriftMartingaleDuality.integrable_inner_of_memLp ((C i).comp_memLp' ht)
      (H.comp_memLp' ((C i).comp_memLp' ht))
  have ha : Integrable (fun ω => inner ℝ (A (R t ω)) (H (R t ω))) μ :=
    DriftMartingaleDuality.integrable_inner_of_memLp (A.comp_memLp' ht) (H.comp_memLp' ht)
  have he : Integrable (fun ω => inner ℝ (R t ω) (H (R t ω))) μ :=
    DriftMartingaleDuality.integrable_inner_of_memLp ht (H.comp_memLp' ht)
  have hi := integral_mono ((integrable_finsetSum Finset.univ (fun i _ => hd i)).add
    (ha.const_mul 2)) (he.const_mul (-ρ)) (fun ω => hq (R t ω))
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_finsetSum Finset.univ (fun i _ => hd i)) (ha.const_mul 2),
    integral_finsetSum _ (fun i _ => hd i),integral_const_mul,integral_const_mul] at hi
  exact hi

theorem integral_generator (T : ℝ≥0) (R : ℝ≥0 → Ω → E)
    (hm : ∀ t, AEStronglyMeasurable (R t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (h2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ)
    (H A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (t : ℝ≥0) (ht : t ≤ T) :
    (∫ s in Ioc 0 (t:ℝ), generator (μ:=μ) R H A C s.toNNReal) =
      (∑ i, ∫ s in Ioc 0 (t:ℝ), ∫ ω, inner ℝ (C i (R s.toNNReal ω))
        (H (C i (R s.toNNReal ω))) ∂μ) +
      2 * ∫ s in Ioc 0 (t:ℝ), ∫ ω, inner ℝ (A (R s.toNNReal ω))
        (H (R s.toNNReal ω)) ∂μ := by
  have he (s : ℝ) (hs : s ∈ Ioc 0 (t:ℝ)) : min s.toNNReal T = s.toNNReal :=
    min_eq_left ((Real.toNNReal_le_iff_le_coe.mpr hs.2).trans ht)
  have hd (i) : IntegrableOn (fun s : ℝ => ∫ ω, inner ℝ (C i (R s.toNNReal ω))
      (H (C i (R s.toNNReal ω))) ∂μ) (Ioc 0 (t:ℝ)) := by
    have h := (ProcessQuadraticInner.continuous_expected_product_clamped T R hm hc h2
      (C i) (H.comp (C i))).integrableOn_Icc (μ := volume) (a := 0) (b := (t:ℝ))
    apply (h.mono_set Ioc_subset_Icc_self).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp only [ContinuousLinearMap.comp_apply,he s hs]
  have ha : IntegrableOn (fun s : ℝ => ∫ ω, inner ℝ (A (R s.toNNReal ω))
      (H (R s.toNNReal ω)) ∂μ) (Ioc 0 (t:ℝ)) := by
    have h := (ProcessQuadraticInner.continuous_expected_product_clamped T R hm hc h2 A H).integrableOn_Icc (μ := volume)
      (a := 0) (b := (t:ℝ))
    apply (h.mono_set Ioc_subset_Icc_self).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp only [he s hs]
  simp only [generator]
  rw [integral_add (integrable_finsetSum Finset.univ (fun i _ => hd i)) (ha.const_mul 2),
    integral_finsetSum _ (fun i _ => hd i),integral_const_mul]

end LinearStochastic.ExpectedQuadraticGenerator
