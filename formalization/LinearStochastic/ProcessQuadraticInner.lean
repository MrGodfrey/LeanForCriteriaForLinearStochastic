module

public import LinearStochastic.SectionHorizonRestriction
public import LinearStochastic.ContinuousQuadraticExpectation

@[expose] public section

/-! Exact conversion of actual predictable L² pairings into expected
quadratic products of the same underlying process, including shorter horizons. -/
noncomputable section
namespace LinearStochastic.ProcessQuadraticInner
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace
open CommonItoMultichannel VectorHorizonRestriction
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {𝓕 : Filtration ℝ≥0 mΩ}

theorem bilinear_inner (T : ℝ≥0) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (R : ℝ≥0 → Ω → E)
    (hr : X =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R)
    (A B : E →L[ℝ] E) :
    inner ℝ (A.compLp X) (B.compLp X) =
      ∫ s in Ioc 0 (T:ℝ), ∫ ω, inner ℝ (A (R s.toNNReal ω)) (B (R s.toNNReal ω)) ∂μ := by
  have hprod : (fun z => inner ℝ (A.compLp X z) (B.compLp X z)) =ᵐ[
      (CommonItoCLM.timeMeasure_T T).prod μ]
      fun z => inner ℝ (A (R z.1 z.2)) (B (R z.1 z.2)) := by
    filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod (A.coeFn_compLp X),
      ae_of_ae_trim 𝓕.predictable_le_prod (B.coeFn_compLp X),hr] with z ha hb hr
    rw [ha,hb,hr]
    rfl
  have he := ((RealTimeBridge.toNNReal_measurePreserving T).prod
    (MeasurePreserving.id μ)).quasiMeasurePreserving.ae_eq_comp hprod
  rw [VectorItoProduct.predictable_inner_real_vector]
  apply integral_congr_ae
  filter_upwards [Measure.ae_ae_of_ae_prod he] with s hs
  exact integral_congr_ae hs

omit [InnerProductSpace ℝ E] in
theorem restrict_representative {t T : ℝ≥0} (h : t ≤ T)
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (R : ℝ≥0 → Ω → E)
    (hr : X =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R) :
    restrict h X =ᵐ[(CommonItoCLM.timeMeasure_T t).prod μ] Function.uncurry R := by
  have hp : (CommonItoCLM.timeMeasure_T t).prod μ ≤ (CommonItoCLM.timeMeasure_T T).prod μ :=
    Measure.prod_mono (Measure.restrict_mono (Ioc_subset_Ioc_right h) le_rfl) le_rfl
  exact Filter.EventuallyEq.trans (ae_of_ae_trim 𝓕.predictable_le_prod (restrict_ae h X))
    (hr.filter_mono (ae_mono hp))

theorem bilinear_restrict_inner {t T : ℝ≥0} (h : t ≤ T)
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (R : ℝ≥0 → Ω → E)
    (hr : X =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R)
    (A B : E →L[ℝ] E) :
    inner ℝ (A.compLp (restrict h X)) (B.compLp (restrict h X)) =
      ∫ s in Ioc 0 (t:ℝ), ∫ ω, inner ℝ (A (R s.toNNReal ω)) (B (R s.toNNReal ω)) ∂μ :=
  bilinear_inner t (restrict h X) R (restrict_representative h X R hr) A B

theorem comp_compLp {Λ : Type*} {mΛ : MeasurableSpace Λ} {ν : Measure Λ}
    (H C : E →L[ℝ] E) (X : Lp E 2 ν) :
    H.compLp (C.compLp X) = (H.comp C).compLp X := by
  apply Lp.ext
  filter_upwards [H.coeFn_compLp (C.compLp X),C.coeFn_compLp X,(H.comp C).coeFn_compLp X]
    with z hh hc hhc
  rw [hh,hc,hhc]
  rfl

theorem continuous_expected_product_clamped (T : ℝ≥0) (R : ℝ≥0 → Ω → E)
    (hm : ∀ t, AEStronglyMeasurable (R t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (h2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ) (A B : E →L[ℝ] E) :
    Continuous (fun s : ℝ => ∫ ω, inner ℝ (A (R (min s.toNNReal T) ω))
      (B (R (min s.toNNReal T) ω)) ∂μ) := by
  exact (ContinuousQuadraticExpectation.continuousOn_expected_product T R hm hc h2 A B).comp_continuous
    (continuous_real_toNNReal.min continuous_const)
    (fun s => show min s.toNNReal T ≤ T from min_le_right _ _)

end LinearStochastic.ProcessQuadraticInner
