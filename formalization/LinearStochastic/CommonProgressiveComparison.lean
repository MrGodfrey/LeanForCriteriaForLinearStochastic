module

public import LinearStochastic.CommonSolutionData

@[expose] public section

/-! Fixed-time modification identities become space-time identities only after
proving joint measurability from actual progressiveness. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonProgressiveComparison
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open CommonItoL2 CommonItoCLM
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- Progressiveness supplies genuinely measurable stopped representatives, so
Fubini may turn fixed-time almost-everywhere equality into product equality. -/
theorem product_ae_of_modification (T : ℝ≥0) {R S : ℝ≥0 → Ω → ℝ}
    (hR : IsProgressive 𝓕 R) (hS : IsProgressive 𝓕 S)
    (he : ∀ t, t ≤ T → R t =ᵐ[μ] S t) :
    Function.uncurry R =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry S := by
  have hr : StronglyMeasurable (fun z : ℝ≥0 × Ω ↦ R (min z.1 T) z.2) :=
    (ProgressivePredictable.progressive_clamp_measurable hR.isStronglyProgressive T).mono
      (sup_le_sup le_rfl (MeasurableSpace.comap_mono (𝓕.le T)))
  have hs : StronglyMeasurable (fun z : ℝ≥0 × Ω ↦ S (min z.1 T) z.2) :=
    (ProgressivePredictable.progressive_clamp_measurable hS.isStronglyProgressive T).mono
      (sup_le_sup le_rfl (MeasurableSpace.comap_mono (𝓕.le T)))
  have hh : (fun z : ℝ≥0 × Ω ↦ R (min z.1 T) z.2) =ᵐ[(timeMeasure_T T).prod μ]
      (fun z ↦ S (min z.1 T) z.2) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hr.measurable hs.measurable)).mpr
    exact Filter.Eventually.of_forall fun t ↦ he (min t T) (min_le_right t T)
  have ht : ∀ᵐ t ∂timeMeasure_T T, t ≤ T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
  filter_upwards [hh,Measure.quasiMeasurePreserving_fst.ae ht] with z hz ht
  simpa only [Function.uncurry,min_eq_left ht] using hz

/-- The actual continuous modifications agree on a single probability-one set
for all times, including the endpoints of the positive horizon. -/
theorem indistinguishable_of_modification (T : ℝ≥0) (hT : 0 < T)
    {R S : ℝ≥0 → Ω → ℝ} (hR : IsProgressive 𝓕 R) (hS : IsProgressive 𝓕 S)
    (hcR : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ R t ω) (Iic T))
    (hcS : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ S t ω) (Iic T))
    (he : ∀ t, t ≤ T → R t =ᵐ[μ] S t) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ T → R t ω = S t ω :=
  CommonContinuousUniqueness.indistinguishable_of_spacetime_ae μ T hT R S hcR hcS
    (product_ae_of_modification T hR hS he)
end LinearStochastic.CommonProgressiveComparison
