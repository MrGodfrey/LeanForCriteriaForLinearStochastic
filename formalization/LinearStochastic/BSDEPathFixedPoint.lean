import LinearStochastic.BSDEPathData
import LinearStochastic.BSDEUniqueness
import LinearStochastic.CommonProgressiveComparison

/-! Arbitrary actual backward paths imply the genuine H² Picard equation.
Neither the initial conditional value nor the fixed-point identity is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BSDEPathFixedPoint
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard BSDEMatrixPicard BSDEPathData
open BSDEProcessLift BSDEIntegralRange CommonInitialPredictable CommonPicardRealization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ : Type*} [Fintype ι] [Fintype κ]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

/-- The terminal range operator equals the actual sum of process-time terminal
integrals, as an equality of actual random variables modulo null sets. -/
theorem integral_terminal_ae (T : ℝ≥0)
    (z : ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    (integral hW hWm hpair hchannels T z : Ω → ℝ) =ᵐ[μ] fun ω ↦
      ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T T (hWm i) (z i) ω := by
  have hh := Lp.coeFn_fun_finsetSum Finset.univ
    (fun i ↦ CommonItoMultichannel.channelIntegral hW hWm i T (z i))
  filter_upwards [hh] with ω hω
  change CommonItoMultichannel.sumIntegral hW hWm T (fun i ↦ z i) ω = _
  rw [CommonItoMultichannel.sumIntegral,hω]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg (fun q : Lp ℝ 2 μ ↦ q ω)
    (CommonItoProcessGeneral.itoProcessCLM_terminal_eq (hW i) T (hWm i) (z i)).symm

include hWc hpair hchannels

/-- A genuine backward Solution record satisfies the actual Picard equation;
its unknown initial F₀ value is recovered from the true terminal decomposition. -/
theorem solution_fixedPoint (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) (η : κ → Lp ℝ 2 μ)
    (q : Solution (𝓕:=𝓕) hW hWm T A C η) :
    BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C η q.X = q.X := by
  have hs (b : κ) := section_memLp hW hWm T A C η q b 0 bot_le
  let ξ : κ → Lp ℝ 2 μ := fun b ↦ (hs b).2.toLp (q.path b 0)
  have hξae (b : κ) : (ξ b : Ω → ℝ) =ᵐ[μ] q.path b 0 := (hs b).2.coeFn_toLp
  have hξ (b : κ) : AEStronglyMeasurable[𝓕 0] (ξ b) μ :=
    (hs b).1.aestronglyMeasurable.congr (hξae b).symm
  have hilift (b : κ) : initialH2 (hs b).1 (hs b).2 T = initialLift T (ξ b) := by
    have hce : μ[ξ b | 𝓕 0] =ᵐ[μ] q.path b 0 := by
      have hh := condExp_congr_ae (m:=𝓕 0) (hξae b)
      rw [condExp_of_stronglyMeasurable (𝓕.le 0) (hs b).1 ((hs b).2.integrable one_le_two)] at hh
      exact hh
    apply Lp.ext
    apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
      𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
    filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod (initialH2_ae (hs b).1 (hs b).2 T),
      ae_of_ae_trim 𝓕.predictable_le_prod (initialLift_ae (𝓕:=𝓕) T (ξ b)),
      Measure.quasiMeasurePreserving_snd.ae hce] with z hi hl hc
    exact hi.trans (hc.symm.trans hl.symm)
  have hstate (b : κ) : q.X.1 b = initialLift T (ξ b) + drift hWm i₀ T (-(driver T A C q.X b)) +
      ∑ i, CommonItoPredictable.itoProcessAssembled (hW i) T (hWm i) (hWc i) (q.X.2 b i) := by
    let R := realization hWm i₀ T (q.path b 0) (-(driver T A C q.X b)) (fun i ↦ q.X.2 b i)
    have he : ∀ t, t ≤ T → q.path b t =ᵐ[μ] R t := by
      intro t ht
      exact (q.equation b t ht).trans
        (realization_integral_identity hW hWm hWc i₀ T (q.path b 0) _ _ ht).symm
    have hp := CommonProgressiveComparison.product_ae_of_modification T (q.progressive b)
      ((realization_predictable hW hWm hWc i₀ T (hs b).1 _ _).isStronglyProgressive.isProgressive) he
    have hc := assembled_ae_realization hW hWm hWc i₀ T (hs b).1 (hs b).2
      (-(driver T A C q.X b)) (fun i ↦ q.X.2 b i)
    rw [hilift b] at hc
    apply Lp.ext
    apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
      𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
    have ha : (initialLift T (ξ b) + drift hWm i₀ T (-(driver T A C q.X b)) +
        ∑ i, CommonItoPredictable.itoProcessAssembled (hW i) T (hWm i) (hWc i) (q.X.2 b i) : H2 𝓕 μ T)
        =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry R :=
      ae_of_ae_trim 𝓕.predictable_le_prod hc
    exact (q.representative b).trans (hp.trans ha.symm)
  have hterminal (b : κ) : η b = ξ b + BSDETerminal.terminal 𝓕 T (-(driver T A C q.X b)) +
      integral hW hWm hpair hchannels T (q.X.2 b) := by
    apply Lp.ext
    filter_upwards [q.terminal b,q.equation b T le_rfl,hξae b,
      BSDETerminal.terminal_ae 𝓕 T (-(driver T A C q.X b)),
      integral_terminal_ae hW hWm hpair hchannels T (q.X.2 b),
      Lp.coeFn_add (ξ b + BSDETerminal.terminal 𝓕 T (-(driver T A C q.X b)))
        (integral hW hWm hpair hchannels T (q.X.2 b)),
      Lp.coeFn_add (ξ b) (BSDETerminal.terminal 𝓕 T (-(driver T A C q.X b)))]
      with ω ht he hx hd hi ha hb
    rw [ha,Pi.add_apply,hb,Pi.add_apply,hx,hd,hi]
    exact ht.symm.trans he
  exact BSDEUniqueness.decomposition_implies_fixedPoint hW hWm hWc hpair hchannels
    i₀ T A C η ξ hξ q.X hstate hterminal

/-- Genuine local uniqueness of both the state and diffusion H² classes. -/
theorem local_classes_unique (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) (η : κ → Lp ℝ 2 μ)
    (q r : Solution (𝓕:=𝓕) hW hWm T A C η)
    (hc : BSDEMatrixPicard.rate T A C < 1) : q.X = r.X := by
  obtain ⟨X,_,hu⟩ := BSDEMatrixPicard.exists_unique_fixedPoint hW hWm hWc hpair hchannels i₀ T A C η hc
  exact (hu q.X (solution_fixedPoint hW hWm hWc hpair hchannels i₀ T A C η q)).trans
    (hu r.X (solution_fixedPoint hW hWm hWc hpair hchannels i₀ T A C η r)).symm

/-- Arbitrary actual backward paths agree on one event throughout a local
interval, including its endpoints; the zero horizon uses its terminal value. -/
theorem local_paths_unique (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) (η : κ → Lp ℝ 2 μ)
    (q r : Solution (𝓕:=𝓕) hW hWm T A C η)
    (hc : BSDEMatrixPicard.rate T A C < 1) :
    ∀ᵐ ω ∂μ, ∀ b t, t ≤ T → q.path b t ω = r.path b t ω := by
  by_cases hT : 0 < T
  · have he := local_classes_unique hW hWm hWc hpair hchannels i₀ T A C η q r hc
    rw [ae_all_iff]
    intro b
    apply CommonContinuousUniqueness.indistinguishable_of_spacetime_ae μ T hT
      (q.path b) (r.path b) (q.continuous b) (r.continuous b)
    have hq := q.representative b
    rw [he] at hq
    exact hq.symm.trans (r.representative b)
  · have hz : T = 0 := le_antisymm (le_of_not_gt hT) zero_le
    rw [ae_all_iff]
    intro b
    filter_upwards [q.terminal b,r.terminal b] with ω hq hr
    intro t ht
    have htT : t = T := le_antisymm ht (hz ▸ zero_le)
    rw [htT]
    exact hq.trans hr.symm

end LinearStochastic.BSDEPathFixedPoint
