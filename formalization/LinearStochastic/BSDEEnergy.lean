import LinearStochastic.DriftMartingaleDuality
import LinearStochastic.RealTimeBridge
import MathFin.Foundations.FiniteMeasureCauchySchwarz

/-! Actual energy estimates used by the backward Picard construction.
All integrals and conditional expectations are Mathlib/constructed operators.
No martingale representation or BSDE existence assertion is assumed proved. -/
noncomputable section
namespace LinearStochastic.BSDEEnergy
open MeasureTheory Set
open scoped NNReal InnerProductSpace
variable {I Ω : Type*} [MeasurableSpace I] [mΩ : MeasurableSpace Ω]
  (ν : Measure I) [IsFiniteMeasure ν] (μ : Measure Ω) [IsFiniteMeasure μ]

/-- Actual time slices of a spacetime L² input are L² almost surely. -/
theorem time_slice_memLp (f : I → Ω → ℝ)
    (hf : MemLp (Function.uncurry f) 2 (ν.prod μ)) :
    ∀ᵐ ω ∂μ, MemLp (fun s => f s ω) 2 ν := by
  filter_upwards [hf.1.prodMk_right,hf.integrable_sq.prod_left_ae] with ω hm hi
  exact (memLp_two_iff_integrable_sq hm).mpr hi

/-- The genuine terminal Lebesgue drift is square integrable. -/
theorem terminal_drift_memLp (f : I → Ω → ℝ)
    (hf : MemLp (Function.uncurry f) 2 (ν.prod μ)) :
    MemLp (fun ω => ∫ s, f s ω ∂ν) 2 μ := by
  have hm := (hf.integrable one_le_two).integral_prod_right.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hm).mpr
  apply (hf.integrable_sq.integral_prod_right.const_mul (ν.real univ)).mono' (hm.pow 2)
  filter_upwards [time_slice_memLp ν μ f hf] with ω hω
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact MathFin.sq_integral_le_measureReal_mul hω

/-- Integrating the true pointwise Cauchy--Schwarz inequality gives the exact
finite-measure terminal energy bound, not an assumed boundedness interface. -/
theorem terminal_drift_energy (f : I → Ω → ℝ)
    (hf : MemLp (Function.uncurry f) 2 (ν.prod μ)) :
    (∫ ω, (∫ s, f s ω ∂ν)^2 ∂μ) ≤
      ν.real univ * ∫ z, (f z.1 z.2)^2 ∂(ν.prod μ) := by
  calc
    _ ≤ ∫ ω, ν.real univ * (∫ s, (f s ω)^2 ∂ν) ∂μ := by
      apply integral_mono_ae (terminal_drift_memLp ν μ f hf).integrable_sq
        (hf.integrable_sq.integral_prod_right.const_mul _)
      exact (time_slice_memLp ν μ f hf).mono (fun ω hω => MathFin.sq_integral_le_measureReal_mul hω)
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      exact (integral_prod_symm _ hf.integrable_sq).symm

/-- Exact L² norm identity for the actual scalar representative. -/
theorem scalar_norm_sq {Λ : Type*} [MeasurableSpace Λ] (P : Measure Λ) (f : Lp ℝ 2 P) :
    ‖f‖^2 = ∫ z, (f z)^2 ∂P := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [Real.inner_apply,pow_two]

/-- Actual pathwise terminal drift, as an L² random variable. -/
def terminalDrift (f : Lp ℝ 2 (ν.prod μ)) : Lp ℝ 2 μ :=
  (terminal_drift_memLp ν μ (Function.curry f) (Lp.memLp f)).toLp
    (fun ω => ∫ s, f (s,ω) ∂ν)

theorem terminalDrift_ae (f : Lp ℝ 2 (ν.prod μ)) :
    terminalDrift ν μ f =ᵐ[μ] fun ω => ∫ s, f (s,ω) ∂ν :=
  (terminal_drift_memLp ν μ (Function.curry f) (Lp.memLp f)).coeFn_toLp

/-- The actual terminal drift operator has norm at most sqrt(time mass). -/
theorem terminalDrift_norm (f : Lp ℝ 2 (ν.prod μ)) :
    ‖terminalDrift ν μ f‖ ≤ Real.sqrt (ν.real univ) * ‖f‖ := by
  have h := terminal_drift_energy ν μ (Function.curry f) (Lp.memLp f)
  have he : ‖terminalDrift ν μ f‖^2 ≤ ν.real univ * ‖f‖^2 := by
    rw [scalar_norm_sq μ,scalar_norm_sq (ν.prod μ)]
    refine (integral_congr_ae ((terminalDrift_ae ν μ f).mono (fun ω hω => congrArg (fun x : ℝ => x^2) hω))).le.trans ?_
    exact h
  have hs : (Real.sqrt (ν.real univ) * ‖f‖)^2 = ν.real univ * ‖f‖^2 := by
    rw [mul_pow,Real.sq_sqrt measureReal_nonneg]
  nlinarith [norm_nonneg (terminalDrift ν μ f),
    mul_nonneg (Real.sqrt_nonneg (ν.real univ)) (norm_nonneg f)]

theorem terminalDrift_add (f g : Lp ℝ 2 (ν.prod μ)) :
    terminalDrift ν μ (f+g) = terminalDrift ν μ f + terminalDrift ν μ g := by
  apply Lp.ext
  have hfg := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae (Lp.coeFn_add f g))
  filter_upwards [terminalDrift_ae ν μ (f+g),terminalDrift_ae ν μ f,terminalDrift_ae ν μ g,
    Lp.coeFn_add (terminalDrift ν μ f) (terminalDrift ν μ g),hfg,
    ((Lp.memLp f).integrable one_le_two).prod_left_ae,
    ((Lp.memLp g).integrable one_le_two).prod_left_ae] with ω hsum hf hg hout hfg hfi hgi
  rw [hsum,hout,Pi.add_apply,hf,hg]
  exact (integral_congr_ae hfg).trans (integral_add hfi hgi)

theorem terminalDrift_smul (c : ℝ) (f : Lp ℝ 2 (ν.prod μ)) :
    terminalDrift ν μ (c • f) = c • terminalDrift ν μ f := by
  apply Lp.ext
  have hcf := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae (Lp.coeFn_smul c f))
  filter_upwards [terminalDrift_ae ν μ (c•f),terminalDrift_ae ν μ f,
    Lp.coeFn_smul c (terminalDrift ν μ f),hcf] with ω hsum hf hout hcf
  rw [hsum,hout,Pi.smul_apply,hf]
  exact (integral_congr_ae hcf).trans (integral_smul c _)

/-- The constructed terminal drift is a genuine continuous linear operator. -/
def terminalDriftCLM : Lp ℝ 2 (ν.prod μ) →L[ℝ] Lp ℝ 2 μ :=
  ({ toFun := terminalDrift ν μ
     map_add' := terminalDrift_add ν μ
     map_smul' := terminalDrift_smul ν μ } : Lp ℝ 2 (ν.prod μ) →ₗ[ℝ] Lp ℝ 2 μ).mkContinuous
      (Real.sqrt (ν.real univ)) (terminalDrift_norm ν μ)

theorem terminalDriftCLM_norm : ‖terminalDriftCLM ν μ‖ ≤ Real.sqrt (ν.real univ) :=
  ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) (terminalDrift_norm ν μ)

/-- Squared norm of an actual L² random variable before quotienting. -/
theorem raw_norm_sq {Λ : Type*} [MeasurableSpace Λ] (P : Measure Λ)
    (f : Λ → ℝ) (hf : MemLp f 2 P) : ‖hf.toLp f‖^2 = ∫ z, (f z)^2 ∂P := by
  rw [scalar_norm_sq P]
  exact integral_congr_ae (hf.coeFn_toLp.mono (fun z hz => congrArg (fun x : ℝ => x^2) hz))

section Martingale
variable [Preorder I]

omit [MeasurableSpace I] [IsFiniteMeasure μ] in
/-- A genuine martingale inherits past L² integrability from its terminal value. -/
theorem martingale_earlier_memLp (𝓕 : Filtration I mΩ) (M : I → Ω → ℝ)
    (hM : Martingale M 𝓕 μ) (s t : I) (hst : s ≤ t) (hMt : MemLp (M t) 2 μ) :
    MemLp (M s) 2 μ :=
  (memLp_congr_ae (hM.2 s t hst)).mp (hMt.condExp one_le_two)

omit [MeasurableSpace I] in
/-- A genuine martingale contracts in L² towards its past, using the actual
conditional-expectation orthogonal projection and only terminal L² as input. -/
theorem martingale_earlier_energy (𝓕 : Filtration I mΩ) (M : I → Ω → ℝ)
    (hM : Martingale M 𝓕 μ) (s t : I) (hst : s ≤ t) (hMt : MemLp (M t) 2 μ) :
    (∫ ω, M s ω ^ 2 ∂μ) ≤ ∫ ω, M t ω ^ 2 ∂μ := by
  have hMs := martingale_earlier_memLp μ 𝓕 M hM s t hst hMt
  have he : (condExpL2 ℝ ℝ (𝓕.le s) (hMt.toLp (M t)) : Lp ℝ 2 μ) = hMs.toLp (M s) := by
    apply Lp.ext
    exact (hMt.condExpL2_ae_eq_condExp (𝕜 := ℝ) (𝓕.le s)).trans
      ((hM.2 s t hst).trans hMs.coeFn_toLp.symm)
  have hn := norm_condExpL2_coe_le (E := ℝ) (𝕜 := ℝ) (𝓕.le s) (hMt.toLp (M t))
  rw [he] at hn
  rw [← raw_norm_sq μ (M s) hMs,← raw_norm_sq μ (M t) hMt]
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- The actual spacetime martingale energy is bounded by time mass times
terminal energy. The input is genuine L² integrability, not this estimate. -/
theorem martingale_time_energy (𝓕 : Filtration I mΩ) (M : I → Ω → ℝ)
    (hM : Martingale M 𝓕 μ) (T : I) (hMT : MemLp (M T) 2 μ)
    (hjoint : MemLp (Function.uncurry M) 2 (ν.prod μ))
    (hT : ∀ᵐ s ∂ν, s ≤ T) :
    (∫ z, M z.1 z.2 ^ 2 ∂(ν.prod μ)) ≤ ν.real univ * ∫ ω, M T ω ^ 2 ∂μ := by
  have he : (∫ z, M z.1 z.2 ^ 2 ∂(ν.prod μ)) = ∫ s, ∫ ω, M s ω ^ 2 ∂μ ∂ν :=
    integral_prod _ hjoint.integrable_sq
  rw [he]
  calc
    _ ≤ ∫ _s, (∫ ω, M T ω ^ 2 ∂μ) ∂ν :=
      integral_mono_ae hjoint.integrable_sq.integral_prod_left (integrable_const _)
        (hT.mono (fun s hs => martingale_earlier_energy μ 𝓕 M hM s T hs hMT))
    _ = _ := by simp [integral_const,smul_eq_mul]

/-- Joint measurability and a genuine martingale's terminal L² bound already
imply spacetime L² on a finite past horizon; it is not postulated as a norm input. -/
theorem martingale_joint_memLp (𝓕 : Filtration I mΩ) (M : I → Ω → ℝ)
    (hM : Martingale M 𝓕 μ) (T : I) (hMT : MemLp (M T) 2 μ)
    (hjoint : AEStronglyMeasurable (Function.uncurry M) (ν.prod μ))
    (hT : ∀ᵐ s ∂ν, s ≤ T) :
    MemLp (Function.uncurry M) 2 (ν.prod μ) := by
  apply (memLp_two_iff_integrable_sq hjoint).mpr
  apply (integrable_prod_iff (hjoint.pow 2)).mpr
  refine ⟨hT.mono (fun s hs => (martingale_earlier_memLp μ 𝓕 M hM s T hs hMT).integrable_sq), ?_⟩
  apply (integrable_const (∫ ω, M T ω ^ 2 ∂μ)).mono' (hjoint.pow 2).norm.integral_prod_right'
  filter_upwards [hT] with s hs
  change ‖∫ ω, ‖M s ω ^ 2‖ ∂μ‖ ≤ _
  have he (ω : Ω) : ‖M s ω ^ 2‖ = M s ω ^ 2 := Real.norm_of_nonneg (sq_nonneg _)
  simp_rw [he]
  rw [Real.norm_of_nonneg (integral_nonneg (fun ω => sq_nonneg (M s ω)))]
  exact martingale_earlier_energy μ 𝓕 M hM s T hs hMT

/-- Full finite-horizon martingale energy from genuine joint measurability and
terminal L² only, as supplied by a continuous martingale version. -/
theorem martingale_energy_of_measurable (𝓕 : Filtration I mΩ) (M : I → Ω → ℝ)
    (hM : Martingale M 𝓕 μ) (T : I) (hMT : MemLp (M T) 2 μ)
    (hjoint : AEStronglyMeasurable (Function.uncurry M) (ν.prod μ))
    (hT : ∀ᵐ s ∂ν, s ≤ T) :
    (∫ z, M z.1 z.2 ^ 2 ∂(ν.prod μ)) ≤ ν.real univ * ∫ ω, M T ω ^ 2 ∂μ :=
  martingale_time_energy ν μ 𝓕 M hM T hMT
    (martingale_joint_memLp ν μ 𝓕 M hM T hMT hjoint hT) hT
end Martingale

end LinearStochastic.BSDEEnergy
