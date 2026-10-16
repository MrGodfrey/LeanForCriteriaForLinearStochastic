import LinearStochastic.CommonRestartIntegral
import LinearStochastic.CommonLocalCoefficients

/-! Deterministic Lebesgue primitive compatibility on actual predictable H²
classes. The same probability-one set works for every restarted time. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonDriftRestart
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonShiftH2
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent W 𝓕 μ]
  (hWm : ∀ t, Measurable (W t))

/-- Prefix restriction preserves all actual Lebesgue primitives simultaneously. -/
theorem primitive_restriction {a T : ℝ≥0} (h : a ≤ T) (g : H2 𝓕 μ T) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ a →
      (∫ s in Ioc (0 : ℝ≥0) t, CommonHorizonRestriction.restriction hWm h g (s,ω) ∂timeMeasure) =
      ∫ s in Ioc (0 : ℝ≥0) t, g (s,ω) ∂timeMeasure := by
  exact CommonLocalCoefficients.primitive_congr_spacetime a
    (ae_of_ae_trim 𝓕.predictable_le_prod (CommonHorizonRestriction.restriction_ae hWm h g))

/-- The actual shifted H² representative has precisely the translated primitive. -/
theorem primitive_shift (a δ T : ℝ≥0) (h : a+δ ≤ T) (g : H2 𝓕 μ T) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ δ →
      (∫ s in Ioc (0 : ℝ≥0) t, shiftCLM a δ T h g (s,ω) ∂timeMeasure) =
      ∫ s in Ioc a (a+t), g (s,ω) ∂timeMeasure := by
  have hh := CommonLocalCoefficients.primitive_congr_spacetime δ
    (f:=fun s ω ↦ shiftCLM a δ T h g (s,ω)) (g:=fun s ω ↦ g (a+s,ω))
    (shift_ae a δ T h g)
  filter_upwards [hh] with ω hω
  intro t ht
  exact (hω t ht).trans (CommonShiftMeasure.integral_shift a t (fun s ↦ g (s,ω)))

/-- The drift restart identity follows from actual slice integrability and the
union of disjoint adjacent intervals; it is not imposed as a solution axiom. -/
theorem primitive_restart (a δ T : ℝ≥0) (h : a+δ ≤ T) (g : H2 𝓕 μ T) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ δ →
      (∫ s in Ioc (0 : ℝ≥0) (a+t), g (s,ω) ∂timeMeasure) =
      (∫ s in Ioc (0 : ℝ≥0) a, g (s,ω) ∂timeMeasure) +
      ∫ s in Ioc (0 : ℝ≥0) t, shiftCLM a δ T h g (s,ω) ∂timeMeasure := by
  filter_upwards [CommonDriftS2.integrand_slice_memLp T g,primitive_shift a δ T h g]
    with ω hω hh
  intro t ht
  rw [hh t ht]
  have hi : IntegrableOn (fun s ↦ g (s,ω)) (Ioc (0 : ℝ≥0) T) timeMeasure :=
    hω.integrable one_le_two
  have hat : a+t ≤ T := (add_le_add le_rfl ht).trans h
  have ha : a ≤ T := (le_add_right le_rfl).trans h
  rw [← Ioc_union_Ioc_eq_Ioc (show 0 ≤ a from zero_le) (le_add_right le_rfl)]
  exact setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
    (hi.mono_set (fun s hs ↦ ⟨hs.1,hs.2.trans ha⟩))
    (hi.mono_set (fun s hs ↦ ⟨lt_of_le_of_lt (show 0 ≤ a from zero_le) hs.1,hs.2.trans hat⟩))
end LinearStochastic.CommonDriftRestart
