import LinearStochastic.VectorHorizonRestriction
import LinearStochastic.SectionLinearDuality

/-! Actual restriction of sectionwise integral solutions, preserving the
specified initial value and using the genuine endpoint at the shorter time. -/
noncomputable section
namespace LinearStochastic.SectionHorizonRestriction
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct LinearDuality SectionLinearDuality VectorHorizonRestriction

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] {𝓕 : Filtration ℝ≥0 mΩ}

theorem real_restrict_ae {t T : ℝ≥0} (h : t ≤ T) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    (fun z : ℝ × Ω => restrict h f (z.1.toNNReal,z.2)) =ᵐ[
      (volume.restrict (Ioc 0 (t:ℝ))).prod μ]
      fun z => f (z.1.toNNReal,z.2) := by
  exact ((RealTimeBridge.toNNReal_measurePreserving t).prod (MeasurePreserving.id μ)).quasiMeasurePreserving.ae_eq_comp
    (ae_of_ae_trim 𝓕.predictable_le_prod (restrict_ae h f))

theorem primitive_restrict [NormedSpace ℝ E] {t T : ℝ≥0} (h : t ≤ T)
    (s : ℝ) (hs : s ≤ t) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    (fun ω => ∫ r in Ioc 0 s, restrict h f (r.toNNReal,ω)) =ᵐ[μ]
      fun ω => ∫ r in Ioc 0 s, f (r.toNNReal,ω) := by
  have he := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae (real_restrict_ae h f))
  filter_upwards [he] with ω he
  exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc_right hs) he)

variable [InnerProductSpace ℝ E] {κ ι : Type*} [Fintype κ] [Fintype ι]
  (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

theorem integralState_restrict {t T : ℝ≥0} (h : t ≤ T) (s : ℝ≥0) (hs : s ≤ t)
    (ξ : Ω → E) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    integralState b hW hWm t ξ (restrict h f) (fun i => restrict h (φ i)) (s:ℝ) =ᵐ[μ]
      integralState b hW hWm T ξ f φ (s:ℝ) := by
  filter_upwards [primitive_restrict h s (by exact_mod_cast hs) f,
    vectorProcess_restrict b hW hWm hs h φ] with ω hd hi
  simp only [integralState,Real.toNNReal_coe,hd,hi]

/-- A prefix has a genuine integral solution once its actual terminal value
is supplied. No endpoint value is extracted from a spacetime equivalence class. -/
theorem section_restrict {t T : ℝ≥0} (h : t ≤ T) (ξ XT Xt : Ω → E)
    (f X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT)
    (hXt : Xt =ᵐ[μ] integralState b hW hWm T ξ f φ (t:ℝ)) :
    SectionIntegralSolution b hW hWm t ξ (restrict h f) (fun i => restrict h (φ i))
      (restrict h X) Xt := by
  constructor
  · have ho := ae_restrict_of_ae_restrict_of_subset
      (Ioc_subset_Ioc_right (show (t:ℝ) ≤ T from h)) hX.sections
    filter_upwards [ho,Measure.ae_ae_of_ae_prod (real_restrict_ae h X),
      ae_restrict_mem measurableSet_Ioc] with s ho hr hs
    have he := integralState_restrict b hW hWm h s.toNNReal
      (Real.toNNReal_le_iff_le_coe.mpr hs.2) ξ f φ
    rw [Real.coe_toNNReal s hs.1.le] at he
    exact Filter.EventuallyEq.trans hr (ho.trans he.symm)
  · exact hXt.trans (integralState_restrict b hW hWm h t le_rfl ξ f φ).symm

end LinearStochastic.SectionHorizonRestriction
