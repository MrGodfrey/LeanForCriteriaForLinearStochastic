import LinearStochastic.ProcessQuadraticInner
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Actual state and feedback H² norms expressed as expected path integrals.
The exponential integral bound is a deterministic consequence of a supplied
pointwise moment estimate; the SDE application proves that estimate separately. -/
noncomputable section
namespace LinearStochastic.ExpectedStateEnergy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace
open CommonItoMultichannel
variable {Ω E U : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] {𝓕 : Filtration ℝ≥0 mΩ}

omit [IsProbabilityMeasure μ] in
theorem id_compLp {Λ : Type*} {mΛ : MeasurableSpace Λ} {ν : Measure Λ} (X : Lp E 2 ν) :
    (ContinuousLinearMap.id ℝ E).compLp X = X := by
  apply Lp.ext
  exact (ContinuousLinearMap.id ℝ E).coeFn_compLp X

theorem norm_sq_eq_integral (T : ℝ≥0) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (R : ℝ≥0 → Ω → E)
    (hr : X =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R) :
    ‖X‖^2 = ∫ s in Ioc 0 (T:ℝ), ∫ ω, ‖R s.toNNReal ω‖^2 ∂μ := by
  have h := ProcessQuadraticInner.bilinear_inner T X R hr
    (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)
  simpa only [id_compLp,ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq] using h

theorem moment_integrable (T : ℝ≥0) (R : ℝ≥0 → Ω → E)
    (hm : ∀ t, AEStronglyMeasurable (R t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (h2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ) :
    IntegrableOn (fun s : ℝ => ∫ ω, ‖R s.toNNReal ω‖^2 ∂μ) (Ioc 0 (T:ℝ)) := by
  have h := (ProcessQuadraticInner.continuous_expected_product_clamped T R hm hc h2
    (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)).integrableOn_Ioc
      (μ:=volume) (a:=0) (b:=(T:ℝ))
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  simp only [ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq,
    min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hs.2)]

omit [IsProbabilityMeasure μ] in
theorem integral_exp_decay_le (T : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) :
    (∫ s in Ioc 0 (T:ℝ), Real.exp (-ρ*s)) ≤ ρ⁻¹ := by
  rw [←intervalIntegral.integral_of_le T.coe_nonneg,
    intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr (ne_of_gt hρ)),
    integral_exp,mul_zero,Real.exp_zero,smul_eq_mul]
  have hh : (-ρ)⁻¹ * (Real.exp (-ρ*(T:ℝ))-1) = ρ⁻¹ * (1-Real.exp (-ρ*(T:ℝ))) := by
    rw [inv_neg]; ring
  rw [hh]
  nlinarith [mul_nonneg (inv_nonneg.mpr hρ.le) (Real.exp_nonneg (-ρ*(T:ℝ)))]

theorem state_energy_le (T : ℝ≥0) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (R : ℝ≥0 → Ω → E)
    (hr : X =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R)
    (hm : ∀ t, AEStronglyMeasurable (R t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (h2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ)
    (M ρ : ℝ) (hM : 0 ≤ M) (hρ : 0 < ρ)
    (hd : ∀ t, t ≤ T → (∫ ω, ‖R t ω‖^2 ∂μ) ≤ M * Real.exp (-ρ*(t:ℝ))) :
    ‖X‖^2 ≤ M/ρ := by
  have he : IntegrableOn (fun s : ℝ => M*Real.exp (-ρ*s)) (Ioc 0 (T:ℝ)) :=
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))) :
      Continuous (fun s : ℝ => M*Real.exp (-ρ*s))).integrableOn_Ioc
  have h := integral_mono_ae (moment_integrable T R hm hc h2) he (by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simpa only [Real.coe_toNNReal s hs.1.le] using hd s.toNNReal
      (Real.toNNReal_le_iff_le_coe.mpr hs.2))
  rw [←norm_sq_eq_integral T X R hr,integral_const_mul] at h
  exact h.trans (by simpa only [div_eq_mul_inv] using
    mul_le_mul_of_nonneg_left (integral_exp_decay_le T ρ hρ) hM)

omit [IsProbabilityMeasure μ] in
theorem feedback_energy_le (T : ℝ≥0) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (K : E →L[ℝ] U) (M ρ : ℝ) (h : ‖X‖^2 ≤ M/ρ) :
    ‖K.compLp X‖^2 ≤ ‖K‖^2 * (M/ρ) := by
  have hn := pow_le_pow_left₀ (norm_nonneg (K.compLp X)) (K.norm_compLp_le X) 2
  rw [mul_pow] at hn
  exact hn.trans (mul_le_mul_of_nonneg_left h (sq_nonneg _))

end LinearStochastic.ExpectedStateEnergy
