module

public import LinearStochastic.CommonItoVersion
public import LinearStochastic.CommonFiltrationCompletion
public import LinearStochastic.CommonItoMultichannel

@[expose] public section

/-! Simultaneous finite-channel repair of Brownian paths on the original
complete filtration, preserving whole-future independence, joint channel laws,
and the actual constructed stochastic integrals. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonBrownianRepair
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open CommonItoIsometry CommonFiltrationCompletion CommonItoCross CommonItoMultichannel
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {ι : Type*} [Fintype ι] {W : ι → ℝ≥0 → Ω → ℝ}
  (hW : ∀ i, IsBrownianReal (W i) μ)

/-- The already constructed continuous Brownian modification, channel by channel. -/
def repaired : ι → ℝ≥0 → Ω → ℝ := fun i ↦ (hW i).toIsPreBrownianReal.mk (W i)

omit [Fintype ι] in
theorem repaired_brownian (i : ι) : IsBrownianReal (repaired hW i) μ :=
  (hW i).toIsPreBrownianReal.isBrownianReal_mk

omit [Fintype ι] in
theorem repaired_continuous (i : ι) (ω : Ω) : Continuous fun t ↦ repaired hW i t ω :=
  (hW i).toIsPreBrownianReal.continuous_mk ω

/-- One event, simultaneously for every finite channel and every real time. -/
theorem repaired_indistinguishable : ∀ᵐ ω ∂μ, ∀ i t, repaired hW i t ω = W i t ω := by
  rw [ae_all_iff]
  exact fun i ↦ (hW i).mk_ae_forall_eq

omit [Fintype ι] in
theorem repaired_paths_ae (i : ι) : (fun ω t ↦ repaired hW i t ω) =ᵐ[μ] (fun ω t ↦ W i t ω) := by
  filter_upwards [(hW i).mk_ae_forall_eq] with ω hω
  exact funext hω

omit [Fintype ι] in
/-- Independent full path laws are preserved, not merely separate marginals. -/
theorem repaired_independent
    (hInd : iIndepFun (fun i ω t ↦ W i t ω) μ) :
    iIndepFun (fun i ω t ↦ repaired hW i t ω) μ :=
  hInd.congr (fun i ↦ (repaired_paths_ae hW i).symm)

omit [Fintype ι] in
theorem repaired_measurable (i : ι) (t : ℝ≥0) : Measurable (repaired hW i t) :=
  (hW i).toIsPreBrownianReal.measurable_mk t

variable {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, ForwardIndependent (W i) 𝓕 μ]

instance repaired_forward (i : ι) : ForwardIndependent (repaired hW i) 𝓕 μ :=
  forwardIndependent_continuous_mk (hW i)


omit [𝓕.IsComplete μ] [∀ i, ForwardIndependent (W i) 𝓕 μ] in
/-- Joint future-vector independence is preserved by the same full-path repair. -/
theorem repaired_pairForward (hp : ∀ i j, PairForwardIndependent (W i) (W j) 𝓕 μ) :
    ∀ i j, PairForwardIndependent (repaired hW i) (repaired hW j) 𝓕 μ := by
  intro i j s
  apply indep_comap_congr _ (hp i j s)
  filter_upwards [repaired_indistinguishable hW] with ω hω
  apply Prod.ext <;> funext u
  · change W i (s+u) ω-W i s ω = repaired hW i (s+u) ω-repaired hW i s ω
    rw [hω i (s+u),hω i s]
  · change W j (s+u) ω-W j s ω = repaired hW j (s+u) ω-repaired hW j s ω
    rw [hω j (s+u),hω j s]

variable [IsProbabilityMeasure μ] (hWm : ∀ i t, Measurable (W i t))

omit [Fintype ι] in
/-- The original and repaired terminal stochastic integrals are the same true
Lp value, on the same filtration and predictable H² domain. -/
theorem repaired_integral (T : ℝ≥0) (i : ι) (f : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    CommonItoCLM.itoIntegralCLM_T (𝓕:=𝓕) (hW i).toIsPreBrownianReal T (hWm i) f =
      CommonItoCLM.itoIntegralCLM_T (𝓕:=𝓕) (repaired_brownian hW i).toIsPreBrownianReal T
        (repaired_measurable hW i) f :=
  CommonItoVersion.integral_congr (hW i).toIsPreBrownianReal
    (repaired_brownian hW i).toIsPreBrownianReal (hWm i)
    (repaired_measurable hW i)
    (by filter_upwards [(hW i).mk_ae_forall_eq] with ω hω using fun t ↦ (hω t).symm) T f

omit [Fintype ι] in
/-- Every constructed process-time integral is unchanged by the joint repair. -/
theorem repaired_process (T t : ℝ≥0) (i : ι) (f : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    CommonItoProcessGeneral.itoProcessCLM (𝓕:=𝓕) (hW i).toIsPreBrownianReal T t (hWm i) f =
      CommonItoProcessGeneral.itoProcessCLM (𝓕:=𝓕) (repaired_brownian hW i).toIsPreBrownianReal T t
        (repaired_measurable hW i) f :=
  CommonItoVersion.process_congr (hW i).toIsPreBrownianReal
    (repaired_brownian hW i).toIsPreBrownianReal (hWm i)
    (repaired_measurable hW i)
    (by filter_upwards [(hW i).mk_ae_forall_eq] with ω hω using fun s ↦ (hω s).symm) T t f

/-- The entire finite-channel integral, rather than just individual channels,
is unchanged as an actual continuous stochastic integral. -/
theorem repaired_sumIntegral (T : ℝ≥0) (f : ι → Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) :
    sumIntegral (𝓕:=𝓕) (fun i ↦ (hW i).toIsPreBrownianReal) hWm T f =
      sumIntegral (𝓕:=𝓕) (fun i ↦ (repaired_brownian hW i).toIsPreBrownianReal)
        (repaired_measurable hW) T f := by
  apply Finset.sum_congr rfl
  intro i _
  exact repaired_integral (𝓕:=𝓕) hW hWm T i (f i)

end LinearStochastic.CommonBrownianRepair
