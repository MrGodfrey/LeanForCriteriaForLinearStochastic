import LinearStochastic.BSDEIntegralRange
import LinearStochastic.BSDETerminal
import LinearStochastic.CommonItoPredictable
import LinearStochastic.CommonDriftPredictable
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! Genuine predictable process lift used for backward iteration.
The initial lift uses actual conditional expectation at F₀; the stochastic lift
uses the already constructed predictable continuous integral representatives. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BSDEProcessLift
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel BSDEIntegralRange
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- Actual conditional-expectation initial representative, constant in time. -/
def initialRaw (χ : Lp ℝ 2 μ) : ℝ≥0 → Ω → ℝ := fun _ ↦ μ[χ | 𝓕 0]

omit [IsProbabilityMeasure μ] in
theorem initialRaw_predictable (χ : Lp ℝ 2 μ) :
    IsStronglyPredictable 𝓕 (initialRaw (𝓕:=𝓕) χ) := by
  have ha : StronglyAdapted 𝓕 (initialRaw (𝓕:=𝓕) χ) := fun t ↦
    (stronglyMeasurable_condExp : StronglyMeasurable[𝓕 0] μ[χ | 𝓕 0]).mono
      (𝓕.mono (show (0 : ℝ≥0) ≤ t from zero_le))
  exact ha.isStronglyPredictable_of_leftContinuous fun _ _ ↦ continuousWithinAt_const

theorem initialRaw_memLp (T : ℝ≥0) (χ : Lp ℝ 2 μ) :
    MemLp (Function.uncurry (initialRaw (𝓕:=𝓕) χ)) 2 (spacetimeMeasure 𝓕 μ T) := by
  have hp := initialRaw_predictable (𝓕:=𝓕) χ
  have hm := ((Lp.memLp χ).condExp one_le_two (m:=𝓕 0)).comp_snd (CommonItoCLM.timeMeasure_T T)
  refine ⟨hp.aestronglyMeasurable, ?_⟩
  change eLpNorm _ 2 (((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod) < ⊤
  rw [eLpNorm_trim _ hp]
  exact hm.2

def initialLift (T : ℝ≥0) (χ : Lp ℝ 2 μ) : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T) :=
  (initialRaw_memLp T χ).toLp (Function.uncurry (initialRaw (𝓕:=𝓕) χ))

theorem initialLift_ae (T : ℝ≥0) (χ : Lp ℝ 2 μ) :
    initialLift (𝓕:=𝓕) T χ =ᵐ[spacetimeMeasure 𝓕 μ T] Function.uncurry (initialRaw (𝓕:=𝓕) χ) :=
  (initialRaw_memLp T χ).coeFn_toLp

/-- Exact norm of the actual constant conditional-expectation process. -/
theorem initialLift_norm_sq (T : ℝ≥0) (χ : Lp ℝ 2 μ) :
    ‖initialLift (𝓕:=𝓕) T χ‖^2 = (T : ℝ) * ‖initialProjection (𝓕:=𝓕) χ‖^2 := by
  have hp := initialRaw_predictable (𝓕:=𝓕) χ
  have hc := (Lp.memLp χ).condExpL2_ae_eq_condExp (𝕜:=ℝ) (𝓕.le 0)
  rw [Lp.toLp_coeFn] at hc
  have hint := (((Lp.memLp χ).condExp one_le_two (m:=𝓕 0)).comp_snd
    (CommonItoCLM.timeMeasure_T T)).integrable_sq
  rw [@BSDEEnergy.scalar_norm_sq (ℝ≥0 × Ω) 𝓕.predictable (spacetimeMeasure 𝓕 μ T) _,
    BSDEEnergy.scalar_norm_sq μ _]
  calc
    _ = ∫ z, (initialRaw (𝓕:=𝓕) χ z.1 z.2)^2 ∂spacetimeMeasure 𝓕 μ T :=
      integral_congr_ae ((initialLift_ae T χ).mono fun z hz ↦ congrArg (fun x : ℝ ↦ x^2) hz)
    _ = ∫ z, (initialRaw (𝓕:=𝓕) χ z.1 z.2)^2 ∂(CommonItoCLM.timeMeasure_T T).prod μ :=
      by simpa only [spacetimeMeasure,Pi.pow_apply,Function.uncurry] using
        (integral_trim (μ := (CommonItoCLM.timeMeasure_T T).prod μ) 𝓕.predictable_le_prod (hp.pow 2)).symm
    _ = ∫ t, ∫ ω, μ[χ | 𝓕 0] ω ^ 2 ∂μ ∂CommonItoCLM.timeMeasure_T T := integral_prod _ hint
    _ = (T : ℝ) * ∫ ω, μ[χ | 𝓕 0] ω ^ 2 ∂μ := by
      rw [integral_const,smul_eq_mul,BSDETerminal.time_mass]
    _ = _ := by
      congr 1
      exact (integral_congr_ae (hc.mono fun ω hω ↦ congrArg (fun x : ℝ ↦ x^2) hω)).symm

theorem initialLift_norm (T : ℝ≥0) (χ : Lp ℝ 2 μ) :
    ‖initialLift (𝓕:=𝓕) T χ‖ ≤ Real.sqrt (T : ℝ) * ‖χ‖ := by
  have hc := norm_condExpL2_coe_le (E:=ℝ) (𝕜:=ℝ) (𝓕.le 0) χ
  have he := initialLift_norm_sq (𝓕:=𝓕) T χ
  have hsq : ‖initialLift (𝓕:=𝓕) T χ‖^2 ≤ (T : ℝ) * ‖χ‖^2 := by
    rw [he]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hc 2) T.coe_nonneg
  have hs : (Real.sqrt (T : ℝ)*‖χ‖)^2 = (T : ℝ)*‖χ‖^2 := by
    rw [mul_pow,Real.sq_sqrt T.coe_nonneg]
  nlinarith [norm_nonneg (initialLift (𝓕:=𝓕) T χ),
    mul_nonneg (Real.sqrt_nonneg (T : ℝ)) (norm_nonneg χ)]

omit [IsProbabilityMeasure μ] in
/-- Equality of actual predictable L² classes can be checked under ambient
space-time measure; this uses measurability in the trimmed sigma algebra. -/
theorem ext_ambient (T : ℝ≥0) {f g : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)}
    (h : (f : ℝ≥0 × Ω → ℝ) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] g) : f = g := by
  apply Lp.ext
  exact ae_eq_trim_of_measurable 𝓕.predictable_le_prod (Lp.stronglyMeasurable f).measurable
    (Lp.stronglyMeasurable g).measurable h

theorem initialLift_sub (T : ℝ≥0) (χ ψ : Lp ℝ 2 μ) :
    initialLift (𝓕:=𝓕) T (χ-ψ) = initialLift (𝓕:=𝓕) T χ - initialLift (𝓕:=𝓕) T ψ := by
  apply ext_ambient T
  have hs : μ[(χ-ψ : Lp ℝ 2 μ) | 𝓕 0] =ᵐ[μ] μ[χ | 𝓕 0] - μ[ψ | 𝓕 0] :=
    (condExp_congr_ae (Lp.coeFn_sub χ ψ)).trans
      (condExp_sub ((Lp.memLp χ).integrable one_le_two) ((Lp.memLp ψ).integrable one_le_two) (𝓕 0))
  have hsp := (Measure.quasiMeasurePreserving_snd (μ := CommonItoCLM.timeMeasure_T T) (ν := μ)).ae hs
  filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod (initialLift_ae T (χ-ψ)),
    ae_of_ae_trim 𝓕.predictable_le_prod (initialLift_ae T χ),
    ae_of_ae_trim 𝓕.predictable_le_prod (initialLift_ae T ψ),
    ae_of_ae_trim 𝓕.predictable_le_prod (Lp.coeFn_sub (initialLift T χ) (initialLift T ψ)),hsp]
    with z hsub hχ hψ hout hs
  rw [hsub,hout,Pi.sub_apply,hχ,hψ]
  exact hs

section Ito
variable {ι : Type*} [Fintype ι] {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

/-- Actual predictable initial-plus-integral process associated to any terminal
variable by conditional projection and the constructed Itô adjoint. -/
def assembled (T : ℝ≥0) (χ : Lp ℝ 2 μ) : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T) :=
  initialLift T χ + ∑ i, CommonItoPredictable.itoProcessAssembled (𝓕:=𝓕) (hW i) T (hWm i) (hWc i)
    (coefficients hW hWm hpair hchannels T χ i)

theorem assembled_sub (T : ℝ≥0) (χ ψ : Lp ℝ 2 μ) :
    assembled hW hWm hWc hpair hchannels T (χ-ψ) =
      assembled hW hWm hWc hpair hchannels T χ - assembled hW hWm hWc hpair hchannels T ψ := by
  unfold assembled
  rw [initialLift_sub]
  have hi (i : ι) : CommonItoPredictable.itoProcessAssembled (𝓕:=𝓕) (μ:=μ) (hW i) T (hWm i) (hWc i)
      (coefficients hW hWm hpair hchannels T (χ-ψ) i) =
      CommonItoPredictable.itoProcessAssembled (𝓕:=𝓕) (μ:=μ) (hW i) T (hWm i) (hWc i)
        (coefficients hW hWm hpair hchannels T χ i) -
      CommonItoPredictable.itoProcessAssembled (𝓕:=𝓕) (μ:=μ) (hW i) T (hWm i) (hWc i)
        (coefficients hW hWm hpair hchannels T ψ i) := by
    rw [map_sub,PiLp.sub_apply]
    exact CommonItoPredictable.itoProcessAssembled_sub (𝓕:=𝓕) (μ:=μ) (hW i) T (hWm i) (hWc i) _ _
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  abel

/-- A direct, dimension-explicit bound for the true assembled process suffices
for Picard contraction; no martingale representation identity is assumed. -/
theorem assembled_norm (T : ℝ≥0) (χ : Lp ℝ 2 μ) :
    ‖assembled hW hWm hWc hpair hchannels T χ‖ ≤
      Real.sqrt (T : ℝ) * (1 + Fintype.card ι) * ‖χ‖ := by
  unfold assembled
  calc
    _ ≤ ‖initialLift T χ‖ + ‖∑ i, CommonItoPredictable.itoProcessAssembled (𝓕:=𝓕) (hW i) T (hWm i) (hWc i)
      (coefficients hW hWm hpair hchannels T χ i)‖ := norm_add_le _ _
    _ ≤ Real.sqrt (T : ℝ) * ‖χ‖ + ∑ i, Real.sqrt (T : ℝ) * ‖χ‖ := by
      apply add_le_add (initialLift_norm T χ)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
      exact (CommonItoPredictable.itoProcessAssembled_norm_le (𝓕:=𝓕) (hW i) T (hWm i) (hWc i) _).trans
        (mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le _ i).trans
          (coefficients_norm hW hWm hpair hchannels T χ)) (Real.sqrt_nonneg _))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

/-- Actual terminal variable whose representation solves the linear backward
step for prescribed driver. The drift integral is the real bounded operator. -/
def terminalInput (T : ℝ≥0) (η : Lp ℝ 2 μ) (f : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) : Lp ℝ 2 μ :=
  η + BSDETerminal.terminal 𝓕 T f

/-- The existing true drift CLM with the common predictable domain made explicit. -/
def drift (i₀ : ι) (T : ℝ≥0) : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T) →L[ℝ]
    Lp ℝ 2 (spacetimeMeasure 𝓕 μ T) :=
  CommonDriftPredictable.driftProcessAssembled (𝓕:=𝓕) (μ:=μ) T (hWm i₀)

/-- First component of the actual backward iteration, in predictable H². -/
def stateStep (i₀ : ι) (T : ℝ≥0) (η : Lp ℝ 2 μ) (f : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    Lp ℝ 2 (spacetimeMeasure 𝓕 μ T) :=
  assembled hW hWm hWc hpair hchannels T (terminalInput T η f) -
    drift hWm i₀ T f

/-- Diffusion component of the actual backward iteration. -/
def diffusionStep (T : ℝ≥0) (η : Lp ℝ 2 μ) (f : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T :=
  coefficients hW hWm hpair hchannels T (terminalInput T η f)

theorem stateStep_difference (i₀ : ι) (T : ℝ≥0) (η : Lp ℝ 2 μ)
    (f g : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    ‖stateStep hW hWm hWc hpair hchannels i₀ T η f - stateStep hW hWm hWc hpair hchannels i₀ T η g‖ ≤
      (T : ℝ) * (2 + Fintype.card ι) * ‖f-g‖ := by
  have he : stateStep hW hWm hWc hpair hchannels i₀ T η f - stateStep hW hWm hWc hpair hchannels i₀ T η g =
      assembled hW hWm hWc hpair hchannels T (BSDETerminal.terminal 𝓕 T (f-g)) -
        drift hWm i₀ T (f-g) := by
    have hfg : η + BSDETerminal.terminal 𝓕 T f - (η + BSDETerminal.terminal 𝓕 T g) =
        BSDETerminal.terminal 𝓕 T f - BSDETerminal.terminal 𝓕 T g := by abel
    have ha := congrArg (assembled hW hWm hWc hpair hchannels T) hfg
    rw [assembled_sub] at ha
    simp only [stateStep,terminalInput,map_sub]
    rw [← ha]
    abel
  rw [he]
  calc
    _ ≤ ‖assembled hW hWm hWc hpair hchannels T (BSDETerminal.terminal 𝓕 T (f-g))‖ +
      ‖drift hWm i₀ T (f-g)‖ := norm_sub_le _ _
    _ ≤ Real.sqrt (T : ℝ) * (1 + Fintype.card ι) * ‖BSDETerminal.terminal 𝓕 T (f-g)‖ +
      (T : ℝ) * ‖f-g‖ := add_le_add (assembled_norm hW hWm hWc hpair hchannels T _)
        (CommonDriftPredictable.driftProcessAssembled_norm_le (𝓕:=𝓕) (μ:=μ) T (hWm i₀) _)
    _ ≤ Real.sqrt (T : ℝ) * (1 + Fintype.card ι) * (Real.sqrt (T : ℝ) * ‖f-g‖) +
      (T : ℝ) * ‖f-g‖ := by
      gcongr
      exact BSDETerminal.terminal_norm 𝓕 T (f-g)
    _ = (Real.sqrt (T : ℝ))^2 * (1 + Fintype.card ι) * ‖f-g‖ + (T : ℝ)*‖f-g‖ := by ring
    _ = _ := by rw [Real.sq_sqrt T.coe_nonneg]; ring

theorem diffusionStep_difference (T : ℝ≥0) (η : Lp ℝ 2 μ)
    (f g : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    ‖diffusionStep hW hWm hpair hchannels T η f - diffusionStep hW hWm hpair hchannels T η g‖ ≤
      Real.sqrt (T : ℝ) * ‖f-g‖ := by
  have he : diffusionStep hW hWm hpair hchannels T η f - diffusionStep hW hWm hpair hchannels T η g =
      coefficients hW hWm hpair hchannels T (BSDETerminal.terminal 𝓕 T (f-g)) := by
    simp only [diffusionStep,terminalInput,map_add,map_sub]
    abel
  rw [he]
  exact (coefficients_norm hW hWm hpair hchannels T _).trans (BSDETerminal.terminal_norm 𝓕 T (f-g))

end Ito
end LinearStochastic.BSDEProcessLift
