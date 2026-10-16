/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

Adapted from ItoProcessPredictable.lean at MathFin commit
99b836298731c432a6242fdb6cb51c1c97f37902. Natural filtration is generalized to
an explicit common filtration. The norm bound uses the proved per-time CLM
contraction directly, so no extra time-indexed-isometry module is imported.
-/

import LinearStochastic.CommonItoContinuous

import BrownianMotion.StochasticIntegral.Predictable

/-! # Predictable space-time L² assembly on a specified common filtration

The elementary integral has continuous paths and is strongly adapted to `𝓕`.
Left continuity implies predictability; taking the pointwise `limUnder` preserves
predictability for the general integral. Tonelli and the per-time L² contraction
prove that this real integral process lies in predictable space-time L², with
norm at most `√T` times the integrand norm. Additivity and subtraction follow
from per-time almost-everywhere equality and Fubini. Brownian paths are assumed
continuous everywhere; a separate complete-filtration construction supplies such
a version on the same probability space.
-/



open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LinearStochastic
namespace CommonItoPredictable
open CommonItoL2 CommonItoCLM CommonItoProcess CommonItoProcessGeneral CommonItoContinuous

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [CommonItoIsometry.ForwardIndependent B 𝓕 μ] (hB : IsPreBrownianReal B μ)

include hB

omit [IsProbabilityMeasure μ] hB in
/-- **Path continuity of the elementary Itô integral.** For every `ω`, the path
`t ↦ (V ● B)_t ω` is continuous: by `itoSimpleProcess_apply` it is a finite sum
`∑_p V(p)(ω) · (B_{p.2 ∧ t}(ω) − B_{p.1 ∧ t}(ω))` of continuous functions of `t`
(Brownian path continuity `hBcont`, composed with the continuous clamp
`t ↦ min c t`). -/
theorem itoSimpleProcess_continuous (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (V : SimpleProcess ℝ 𝓕) (ω : Ω) :
    Continuous (fun t : ℝ≥0 ↦ itoSimpleProcess hBmeas V t ω) := by
  simp_rw [itoSimpleProcess_apply hBmeas V, Finsupp.sum]
  refine continuous_finsetSum _ (fun p _ ↦ ?_)
  refine Continuous.const_mul ?_ _
  exact ((hBcont ω).comp (continuous_const.min continuous_id)).sub
    ((hBcont ω).comp (continuous_const.min continuous_id))

omit [IsProbabilityMeasure μ] in
/-- **The elementary Itô integral is predictable** as a space-time function. It is
genuinely (every `ω`) continuous — hence left-continuous — and genuinely adapted
(the martingale property `itoSimpleProcess_isMartingale.1`), so Degenne's
`StronglyAdapted.isStronglyPredictable_of_leftContinuous` applies directly. This
is the base case that sidesteps the a.e./everywhere friction which blocks
applying the same lemma to the continuous modification directly. -/
theorem itoSimpleProcess_isStronglyPredictable (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (V : SimpleProcess ℝ 𝓕) :
    IsStronglyPredictable 𝓕 (itoSimpleProcess hBmeas V) := by
  apply MeasureTheory.StronglyAdapted.isStronglyPredictable_of_leftContinuous
  · exact (itoSimpleProcess_isMartingale hB hBmeas V).1
  · exact fun ω a ↦ (itoSimpleProcess_continuous hBmeas hBcont V ω).continuousWithinAt

/-- **The assembled Itô process is predictable** (general integrand). By
construction `itoContinuousMod` is the pointwise `limUnder` of the elementary
integrals of a fixed approximating sequence `Vₙ`; each is predictable
(`itoSimpleProcess_isStronglyPredictable`), and `StronglyMeasurable.limUnder`
lifts strong predictable-measurability to the limit. (The ambient σ-algebra must
be pinned to the predictable one before invoking the limit lemma, which would
otherwise synthesize the default product σ-algebra.) -/
theorem itoContinuousMod_isStronglyPredictable (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    IsStronglyPredictable 𝓕 (itoContinuousMod T hBmeas φ) := by
  rw [IsStronglyPredictable]
  have hrw : (Function.uncurry (itoContinuousMod T hBmeas φ))
      = fun z : ℝ≥0 × Ω ↦ limUnder atTop (fun n ↦
          Function.uncurry (itoSimpleProcess hBmeas
            ((approxSeq T hBmeas φ).choose n).val) z) := by
    funext z; rfl
  rw [hrw]
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  exact StronglyMeasurable.limUnder (fun n ↦
    itoSimpleProcess_isStronglyPredictable hB hBmeas hBcont
      ((approxSeq T hBmeas φ).choose n).val)

/-- **The assembled Itô process is `L²`** in the predictable trim measure. It is predictable
(`itoContinuousMod_isStronglyPredictable`); the energy is finite because, slice by slice, the
modification identity and the Itô contraction give `∫₀ᵀ ‖(φ ● B)_t‖² dt ≤ T ‖φ‖²` (`eLpNorm_trim`
drops the trim, then Tonelli splits the product and each time-slice is bounded by
`itoProcessCLM_norm_le`). -/
theorem memLp_itoContinuousMod (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    MemLp (Function.uncurry (itoContinuousMod T hBmeas φ)) 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas) := by
  have hpred := itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont φ
  refine ⟨hpred.aestronglyMeasurable, ?_⟩
  rw [show trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas
        = ((timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod from rfl,
      eLpNorm_trim _ hpred,
      eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num),
      lintegral_prod _
        ((hpred.mono 𝓕.predictable_le_prod).measurable.enorm.pow_const _
          |>.aemeasurable)]
  -- per-time energy bound: for `t ≤ T` the slice energy is `≤ ‖φ‖²`
  have key : ∀ t : ℝ≥0, t ≤ T →
      (∫⁻ ω, ‖itoContinuousMod T hBmeas φ t ω‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ)
        ≤ (ENNReal.ofReal ‖φ‖) ^ (2 : ℝ≥0∞).toReal := by
    intro t htT
    have hmod : (∫⁻ ω, ‖itoContinuousMod T hBmeas φ t ω‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ)
        = ∫⁻ ω, ‖(itoProcessCLM hB T t hBmeas φ : Ω → ℝ) ω‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont φ htT] with ω hω
      rw [hω]
    rw [hmod, lintegral_rpow_enorm_eq_rpow_eLpNorm' (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
    gcongr
    rw [← eLpNorm_eq_eLpNorm' (by norm_num) (by norm_num), ← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (itoProcessCLM_norm_le hB T t hBmeas φ)
  refine lt_of_le_of_lt
    (lintegral_mono_ae (g := fun _ ↦ (ENNReal.ofReal ‖φ‖) ^ (2 : ℝ≥0∞).toReal) ?_) ?_
  · have hsub : ∀ᵐ t ∂(timeMeasure_T T), t ≤ T := by
      rw [timeMeasure_T]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
    filter_upwards [hsub] with t htT using key t htT
  · rw [lintegral_const]
    exact ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) (measure_lt_top _ _)

/-- **The assembled Itô process as an element of the predictable `L²` space `E`.**
The space-time function `(t,ω) ↦ (φ ● B)_t(ω)` (the continuous modification), packaged as a
class in `Lp ℝ 2 (trimMeasure_T T)` — the object a Picard iterate for the SDE lands in. -/
noncomputable def itoProcessAssembled (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas) :=
  (memLp_itoContinuousMod hB T hBmeas hBcont φ).toLp (Function.uncurry (itoContinuousMod T hBmeas φ))

/-- **The energy identity.** `‖itoProcessAssembled φ‖²_E = ∫₀ᵀ ‖(φ ● B)_t‖² dt` — the squared
`E`-norm of the assembled process is the time-integral of the per-time Itô `L²`-norms. Slice by
slice the modification identity turns the space-time integral (Tonelli over the trimmed product)
into `∫₀ᵀ ‖itoProcessCLM T t φ‖² dt`. The existing per-time contraction
then supplies the space-time norm bound used in the Picard estimate. -/
theorem itoProcessAssembled_norm_sq (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    ‖itoProcessAssembled hB T hBmeas hBcont φ‖ ^ 2
      = ∫ t, ‖itoProcessCLM hB T t hBmeas φ‖ ^ 2 ∂(timeMeasure_T T) := by
  have hpred := itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont φ
  have hmem := memLp_itoContinuousMod hB T hBmeas hBcont φ
  have hmem_prod : MemLp (Function.uncurry (itoContinuousMod T hBmeas φ)) 2
      ((timeMeasure_T T).prod μ) := by
    refine ⟨(hpred.mono 𝓕.predictable_le_prod).aestronglyMeasurable, ?_⟩
    rw [← eLpNorm_trim 𝓕.predictable_le_prod hpred]
    exact hmem.2
  have hint : Integrable (fun z ↦ (Function.uncurry (itoContinuousMod T hBmeas φ) z) ^ 2)
      ((timeMeasure_T T).prod μ) := by
    refine (hmem_prod.integrable_mul hmem_prod).congr ?_
    filter_upwards with z
    rw [Pi.mul_apply, pow_two]
  have hcoe : ⇑(itoProcessAssembled hB T hBmeas hBcont φ)
      =ᵐ[trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas φ) :=
    hmem.coeFn_toLp
  have htrim : (∫ z, (Function.uncurry (itoContinuousMod T hBmeas φ) z) ^ 2
        ∂(trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas))
      = ∫ z, (Function.uncurry (itoContinuousMod T hBmeas φ) z) ^ 2 ∂((timeMeasure_T T).prod μ) :=
    (integral_trim (μ := (timeMeasure_T T).prod μ)
      𝓕.predictable_le_prod (hpred.pow 2)).symm
  rw [lp_two_norm_sq,
      integral_congr_ae (g := fun z ↦ (Function.uncurry (itoContinuousMod T hBmeas φ) z) ^ 2)
        (by filter_upwards [hcoe] with z hz; rw [hz]),
      htrim, integral_prod _ hint]
  refine integral_congr_ae ?_
  have hsub : ∀ᵐ t ∂(timeMeasure_T T), t ≤ T := by
    rw [timeMeasure_T]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
  filter_upwards [hsub] with t htT
  rw [lp_two_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont φ htT] with ω hω
  simp only [Function.uncurry]
  rw [hω]

/-- **The Itô operator bound** `‖itoProcessAssembled φ‖ ≤ √T‖φ‖` — the norm corollary of the energy
identity `itoProcessAssembled_norm_sq`: it turns the square norm into `∫₀ᵀ ‖itoProcessCLM t φ‖² dt`,
and each per-time squared norm is bounded by the full integrand energy `‖φ‖²`, so the
time-integral is `≤ T‖φ‖²`. The `√T` (vs the drift's `T`) is the contraction workhorse. -/
theorem itoProcessAssembled_norm_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    ‖itoProcessAssembled hB T hBmeas hBcont φ‖ ≤ Real.sqrt (T : ℝ) * ‖φ‖ := by
  have hφsq : Integrable (fun z ↦ (φ z) ^ 2) (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas) :=
    (Lp.memLp φ).integrable_sq
  have hsq : ‖itoProcessAssembled hB T hBmeas hBcont φ‖ ^ 2 ≤ (T : ℝ) * ‖φ‖ ^ 2 := by
    rw [itoProcessAssembled_norm_sq]
    have hpt : ∀ᵐ t ∂(timeMeasure_T T),
        ‖itoProcessCLM hB T t hBmeas φ‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
      filter_upwards [ae_restrict_mem (μ := timeMeasure) measurableSet_Ioc] with t ht
      exact pow_le_pow_left₀ (norm_nonneg _) (itoProcessCLM_norm_le hB T t hBmeas φ) 2
    calc ∫ t, ‖itoProcessCLM hB T t hBmeas φ‖ ^ 2 ∂(timeMeasure_T T)
        ≤ ∫ _t, ‖φ‖ ^ 2 ∂(timeMeasure_T T) :=
          integral_mono_of_nonneg (ae_of_all _ fun _ ↦ sq_nonneg _) (integrable_const _) hpt
      _ = (T : ℝ) * ‖φ‖ ^ 2 := by
          rw [integral_const, timeMeasure_T, measureReal_def, Measure.restrict_apply_univ,
            timeMeasure_Ioc,
            ENNReal.toReal_ofReal (by rw [NNReal.coe_zero, sub_zero]; exact T.coe_nonneg),
            NNReal.coe_zero, sub_zero, smul_eq_mul]
  have h := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul T.coe_nonneg, Real.sqrt_sq (norm_nonneg _)] at h

/-- **Additivity** of the assembled Itô process (as an `Lp` class). Both sides are modifications
of the linear process `itoProcessCLM T · (φ+ψ)`, so they agree slice by slice (the modification
identity + `itoProcessCLM`'s `map_add`); the per-time a.e. equalities lift to an a.e. equality on
the trimmed product (`Measure.ae_prod_iff_ae_ae` + `ae_eq_trim_of_stronglyMeasurable`). -/
theorem itoProcessAssembled_add (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ ψ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    itoProcessAssembled hB T hBmeas hBcont (φ + ψ)
      = itoProcessAssembled hB T hBmeas hBcont φ + itoProcessAssembled hB T hBmeas hBcont ψ := by
  have hpredφ := itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont φ
  have hpredψ := itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont ψ
  have hpredS' : StronglyMeasurable[𝓕.predictable]
      (Function.uncurry (itoContinuousMod T hBmeas (φ + ψ))) :=
    itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont (φ + ψ)
  have hgSM : StronglyMeasurable[𝓕.predictable]
      (Function.uncurry (itoContinuousMod T hBmeas φ)
        + Function.uncurry (itoContinuousMod T hBmeas ψ)) :=
    StronglyMeasurable.add hpredφ hpredψ
  have hkey : Function.uncurry (itoContinuousMod T hBmeas (φ + ψ))
      =ᵐ[trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas]
        (Function.uncurry (itoContinuousMod T hBmeas φ)
          + Function.uncurry (itoContinuousMod T hBmeas ψ)) := by
    refine hpredS'.ae_eq_trim_of_stronglyMeasurable
      𝓕.predictable_le_prod hgSM ?_
    have hset : MeasurableSet {z : ℝ≥0 × Ω |
        Function.uncurry (itoContinuousMod T hBmeas (φ + ψ)) z
          = (Function.uncurry (itoContinuousMod T hBmeas φ)
              + Function.uncurry (itoContinuousMod T hBmeas ψ)) z} :=
      measurableSet_eq_fun (hpredS'.mono 𝓕.predictable_le_prod).measurable
        (hgSM.mono 𝓕.predictable_le_prod).measurable
    rw [Filter.EventuallyEq, Measure.ae_prod_iff_ae_ae hset]
    have hsub : ∀ᵐ t ∂(timeMeasure_T T), t ≤ T := by
      rw [timeMeasure_T]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
    filter_upwards [hsub] with t htT
    filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont (φ + ψ) htT,
      itoContinuousMod_modification hB T hBmeas hBcont φ htT,
      itoContinuousMod_modification hB T hBmeas hBcont ψ htT,
      Lp.coeFn_add (itoProcessCLM hB T t hBmeas φ) (itoProcessCLM hB T t hBmeas ψ)]
      with ω hωS hωφ hωψ hωadd
    simp only [Function.uncurry, Pi.add_apply]
    rw [hωS, map_add, hωadd, Pi.add_apply, ← hωφ, ← hωψ]
  have hcoeS : ⇑(itoProcessAssembled hB T hBmeas hBcont (φ + ψ))
      =ᵐ[trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas (φ + ψ)) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont (φ + ψ)).coeFn_toLp
  have hcoeφ : ⇑(itoProcessAssembled hB T hBmeas hBcont φ)
      =ᵐ[trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas φ) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont φ).coeFn_toLp
  have hcoeψ : ⇑(itoProcessAssembled hB T hBmeas hBcont ψ)
      =ᵐ[trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas ψ) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont ψ).coeFn_toLp
  refine Lp.ext ?_
  filter_upwards [hcoeS, hkey, hcoeφ, hcoeψ,
    Lp.coeFn_add (itoProcessAssembled hB T hBmeas hBcont φ)
      (itoProcessAssembled hB T hBmeas hBcont ψ)] with z hzS hzk hzφ hzψ hza
  rw [hzS, hzk, hza]
  simp only [Pi.add_apply, hzφ, hzψ]

/-- **Subtractivity** of the assembled Itô process (the SDE contraction consumes this: it turns
`itoProcessAssembled (σ∘X) − itoProcessAssembled (σ∘Y)` into `itoProcessAssembled (σ∘X − σ∘Y)`, whose
energy is `∫₀ᵀ ‖itoProcessCLM T t (σ∘X − σ∘Y)‖² dt`). -/
theorem itoProcessAssembled_sub (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ ψ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    itoProcessAssembled hB T hBmeas hBcont (φ - ψ)
      = itoProcessAssembled hB T hBmeas hBcont φ - itoProcessAssembled hB T hBmeas hBcont ψ := by
  have hpredφ := itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont φ
  have hpredψ := itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont ψ
  have hpredS' : StronglyMeasurable[𝓕.predictable]
      (Function.uncurry (itoContinuousMod T hBmeas (φ - ψ))) :=
    itoContinuousMod_isStronglyPredictable hB T hBmeas hBcont (φ - ψ)
  have hgSM : StronglyMeasurable[𝓕.predictable]
      (Function.uncurry (itoContinuousMod T hBmeas φ)
        - Function.uncurry (itoContinuousMod T hBmeas ψ)) :=
    StronglyMeasurable.sub hpredφ hpredψ
  have hkey : Function.uncurry (itoContinuousMod T hBmeas (φ - ψ))
      =ᵐ[trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas]
        (Function.uncurry (itoContinuousMod T hBmeas φ)
          - Function.uncurry (itoContinuousMod T hBmeas ψ)) := by
    refine hpredS'.ae_eq_trim_of_stronglyMeasurable
      𝓕.predictable_le_prod hgSM ?_
    have hset : MeasurableSet {z : ℝ≥0 × Ω |
        Function.uncurry (itoContinuousMod T hBmeas (φ - ψ)) z
          = (Function.uncurry (itoContinuousMod T hBmeas φ)
              - Function.uncurry (itoContinuousMod T hBmeas ψ)) z} :=
      measurableSet_eq_fun (hpredS'.mono 𝓕.predictable_le_prod).measurable
        (hgSM.mono 𝓕.predictable_le_prod).measurable
    rw [Filter.EventuallyEq, Measure.ae_prod_iff_ae_ae hset]
    have hsub : ∀ᵐ t ∂(timeMeasure_T T), t ≤ T := by
      rw [timeMeasure_T]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
    filter_upwards [hsub] with t htT
    filter_upwards [itoContinuousMod_modification hB T hBmeas hBcont (φ - ψ) htT,
      itoContinuousMod_modification hB T hBmeas hBcont φ htT,
      itoContinuousMod_modification hB T hBmeas hBcont ψ htT,
      Lp.coeFn_sub (itoProcessCLM hB T t hBmeas φ) (itoProcessCLM hB T t hBmeas ψ)]
      with ω hωS hωφ hωψ hωsub
    simp only [Function.uncurry, Pi.sub_apply]
    rw [hωS, map_sub, hωsub, Pi.sub_apply, ← hωφ, ← hωψ]
  have hcoeS : ⇑(itoProcessAssembled hB T hBmeas hBcont (φ - ψ))
      =ᵐ[trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas (φ - ψ)) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont (φ - ψ)).coeFn_toLp
  have hcoeφ : ⇑(itoProcessAssembled hB T hBmeas hBcont φ)
      =ᵐ[trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas φ) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont φ).coeFn_toLp
  have hcoeψ : ⇑(itoProcessAssembled hB T hBmeas hBcont ψ)
      =ᵐ[trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas] Function.uncurry (itoContinuousMod T hBmeas ψ) :=
    (memLp_itoContinuousMod hB T hBmeas hBcont ψ).coeFn_toLp
  refine Lp.ext ?_
  filter_upwards [hcoeS, hkey, hcoeφ, hcoeψ,
    Lp.coeFn_sub (itoProcessAssembled hB T hBmeas hBcont φ)
      (itoProcessAssembled hB T hBmeas hBcont ψ)] with z hzS hzk hzφ hzψ hza
  rw [hzS, hzk, hza]
  simp only [Pi.sub_apply, hzφ, hzψ]

end CommonItoPredictable
end LinearStochastic
