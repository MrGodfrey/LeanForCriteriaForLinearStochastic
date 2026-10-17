module

public import LinearStochastic.BSDEMatrixPicard
public import LinearStochastic.CommonStateS2

@[expose] public section

/-! Actual continuous predictable realization of a represented backward step.
The only representation hypothesis is the explicit membership in the genuine
constructed Itô range; no martingale representation theorem is presumed. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BSDERealization
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonItoMultichannel CommonVectorPicard BSDEIntegralRange BSDEProcessLift
open CommonPicardRealization CommonInitialPredictable
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

theorem initialH2_eq_initialLift (T : ℝ≥0) (χ : Lp ℝ 2 μ) :
    initialH2 (𝓕:=𝓕) (stronglyMeasurable_condExp (m:=𝓕 0))
      ((Lp.memLp χ).condExp one_le_two) T = initialLift (𝓕:=𝓕) T χ := by
  apply Lp.ext
  exact (initialH2_ae (stronglyMeasurable_condExp (m:=𝓕 0))
    ((Lp.memLp χ).condExp one_le_two) T).trans (initialLift_ae T χ).symm

/-- Actual backward path from initial conditional expectation, negative drift,
and the constructed continuous Itô modifications. -/
def path (i₀ : ι) (T : ℝ≥0) (η : Lp ℝ 2 μ) (f : H2 𝓕 μ T) : ℝ≥0 → Ω → ℝ :=
  realization hWm i₀ T μ[terminalInput T η f | 𝓕 0] (-f)
    (fun i ↦ diffusionStep hW hWm hpair hchannels T η f i)

include hWc

theorem path_predictable (i₀ : ι) (T : ℝ≥0) (η : Lp ℝ 2 μ) (f : H2 𝓕 μ T) :
    IsStronglyPredictable 𝓕 (path hW hWm hpair hchannels i₀ T η f) :=
  realization_predictable hW hWm hWc i₀ T stronglyMeasurable_condExp _ _

theorem path_continuousOn (i₀ : ι) (T : ℝ≥0) (η : Lp ℝ 2 μ) (f : H2 𝓕 μ T) :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ path hW hWm hpair hchannels i₀ T η f t ω) (Icc 0 T) :=
  realization_continuousOn hW hWm hWc i₀ T _ _ _

/-- Identification with the actual predictable H² backward step. -/
theorem stateStep_ae_path (i₀ : ι) (T : ℝ≥0) (η : Lp ℝ 2 μ) (f : H2 𝓕 μ T) :
    stateStep hW hWm hWc hpair hchannels i₀ T η f =ᵐ[spacetimeMeasure 𝓕 μ T]
      Function.uncurry (path hW hWm hpair hchannels i₀ T η f) := by
  let χ := terminalInput T η f
  have he : initialH2 (𝓕:=𝓕) (stronglyMeasurable_condExp (f:=χ) (m:=𝓕 0))
      ((Lp.memLp χ).condExp one_le_two) T + driftScalar hWm i₀ T (-f) +
        ∑ i, itoScalar hW hWm hWc i T (diffusionStep hW hWm hpair hchannels T η f i) =
      stateStep hW hWm hWc hpair hchannels i₀ T η f := by
    rw [initialH2_eq_initialLift,map_neg]
    change initialLift T χ + -(drift hWm i₀ T f) +
      ∑ i, CommonItoPredictable.itoProcessAssembled (hW i) T (hWm i) (hWc i) (coefficients hW hWm hpair hchannels T χ i) =
      initialLift T χ + (∑ i, CommonItoPredictable.itoProcessAssembled (hW i) T (hWm i) (hWc i) (coefficients hW hWm hpair hchannels T χ i)) - drift hWm i₀ T f
    abel
  rw [← he]
  exact assembled_ae_realization hW hWm hWc i₀ T stronglyMeasurable_condExp
    ((Lp.memLp χ).condExp one_le_two) (-f) _

/-- The actual path has the true conditional initial value, independently of
space-time equivalence which does not control the endpoint zero. -/
theorem path_initial (i₀ : ι) (T : ℝ≥0) (η : Lp ℝ 2 μ) (f : H2 𝓕 μ T) :
    path hW hWm hpair hchannels i₀ T η f 0 =ᵐ[μ] μ[terminalInput T η f | 𝓕 0] :=
  realization_initial hW hWm hWc i₀ T _ _ _

/-- Fixed-time integral identity, obtained from actual constructed operators. -/
theorem path_integral_identity (i₀ : ι) (T : ℝ≥0) (η : Lp ℝ 2 μ) (f : H2 𝓕 μ T)
    {t : ℝ≥0} (ht : t ≤ T) :
    path hW hWm hpair hchannels i₀ T η f t =ᵐ[μ] fun ω ↦
      μ[terminalInput T η f | 𝓕 0] ω +
      (∫ s in Ioc (0 : ℝ≥0) t, (-f : H2 𝓕 μ T) (s,ω) ∂CommonItoL2.timeMeasure) +
      ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i)
        (diffusionStep hW hWm hpair hchannels T η f i) ω :=
  realization_integral_identity hW hWm hWc i₀ T _ _ _ ht

/-- Representation in the true range enforces the terminal boundary value. -/
theorem path_terminal (i₀ : ι) (T : ℝ≥0) (η : Lp ℝ 2 μ) (f : H2 𝓕 μ T)
    (hr : Represented hW hWm hpair hchannels T (terminalInput T η f)) :
    path hW hWm hpair hchannels i₀ T η f T =ᵐ[μ] η := by
  let χ := terminalInput T η f
  let z := coefficients hW hWm hpair hchannels T χ
  have he : initialProjection (𝓕:=𝓕) χ + BSDETerminal.terminal 𝓕 T (-f) +
      integral hW hWm hpair hchannels T z = η := by
    have hh := (represented_iff hW hWm hpair hchannels T χ).mp hr
    have hi : χ = η + BSDETerminal.terminal 𝓕 T f := rfl
    rw [map_neg]
    calc
      _ = (initialProjection (𝓕:=𝓕) χ + integral hW hWm hpair hchannels T z) - BSDETerminal.terminal 𝓕 T f := by abel
      _ = χ - BSDETerminal.terminal 𝓕 T f := by rw [← hh]
      _ = η := by rw [hi]; abel
  have hce := (Lp.memLp χ).condExpL2_ae_eq_condExp (𝕜:=ℝ) (𝓕.le 0)
  rw [Lp.toLp_coeFn] at hce
  change (initialProjection (𝓕:=𝓕) χ : Ω → ℝ) =ᵐ[μ] μ[χ | 𝓕 0] at hce
  have hz : ∀ᵐ ω ∂μ, (integral hW hWm hpair hchannels T z) ω =
      ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T T (hWm i) (z i) ω := by
    have hh := Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ channelIntegral hW hWm i T (z i))
    filter_upwards [hh] with ω hω
    change (sumIntegral hW hWm T (fun i ↦ z i)) ω = _
    rw [sumIntegral,hω]
    exact Finset.sum_congr rfl fun i _ ↦ congrArg (fun q : Lp ℝ 2 μ ↦ q ω)
      (CommonItoProcessGeneral.itoProcessCLM_terminal_eq (hW i) T (hWm i) (z i)).symm
  have heae : (initialProjection (𝓕:=𝓕) χ + BSDETerminal.terminal 𝓕 T (-f) +
      integral hW hWm hpair hchannels T z : Lp ℝ 2 μ) =ᵐ[μ] η := by rw [he]
  filter_upwards [path_integral_identity hW hWm hWc hpair hchannels i₀ T η f le_rfl,
    BSDETerminal.terminal_ae 𝓕 T (-f),hce,hz,heae,
    Lp.coeFn_add (initialProjection (𝓕:=𝓕) χ + BSDETerminal.terminal 𝓕 T (-f))
      (integral hW hWm hpair hchannels T z),
    Lp.coeFn_add (initialProjection (𝓕:=𝓕) χ) (BSDETerminal.terminal 𝓕 T (-f))]
    with ω hp hd hc hz he ha hb
  rw [ha,Pi.add_apply,hb,Pi.add_apply,hc,hd,hz] at he
  exact hp.trans he

/-- The path has actual square-integrable path supremum on complete filtrations. -/
theorem path_S2 [𝓕.IsComplete μ] (i₀ : ι) (T : ℝ≥0)
    (η : Lp ℝ 2 μ) (f : H2 𝓕 μ T) :
    MemLp (ContinuousDoobL2.pathSup (path hW hWm hpair hchannels i₀ T η f) T) 2 μ :=
  CommonStateS2.realization_S2 hW hWm hWc i₀ T stronglyMeasurable_condExp
    ((Lp.memLp (terminalInput T η f)).condExp one_le_two) _ _

end LinearStochastic.BSDERealization
