module

public import LinearStochastic.BSDEPathFixedPoint
public import LinearStochastic.BSDEPathRestriction
public import LinearStochastic.BSDEGlobalExistence

@[expose] public section

/-! Global uniqueness of genuine backward solutions is obtained by actual
reverse interval restriction, local Picard uniqueness and exact H² pasting.
Martingale representation and the desired uniqueness are not premises. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BSDEGlobalUniqueness
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonVectorPicard BSDEMatrixPicard BSDEPathData BSDEPathFixedPoint BSDEPathRestriction
open CommonHorizonRestriction CommonShiftH2 CommonShiftSimple
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ : Type*} [Fintype ι] [Fintype κ]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

include hWc hpair hchannels

/-- Reverse finite-mesh uniqueness preserves both state and diffusion classes,
and identifies the continuous paths on one probability-one event. -/
theorem unique_grid (i₀ : ι) (δ : ℝ≥0)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (hc : BSDEMatrixPicard.rate δ A C < 1) :
    ∀ N : ℕ, ∀ η : κ → Lp ℝ 2 μ,
      ∀ q r : Solution (𝓕:=𝓕) hW hWm ((N:ℝ≥0)*δ) A C η,
        q.X = r.X ∧ (∀ᵐ ω ∂μ, ∀ b t, t ≤ (N:ℝ≥0)*δ → q.path b t ω = r.path b t ω) := by
  intro N
  induction N with
  | zero =>
    intro η q r
    have hz : BSDEMatrixPicard.rate ((0:ℝ≥0)*δ) A C < 1 := by simp [BSDEMatrixPicard.rate]
    exact ⟨local_classes_unique hW hWm hWc hpair hchannels i₀ _ A C η q r (by simpa only [Nat.cast_zero] using hz),
      local_paths_unique hW hWm hWc hpair hchannels i₀ _ A C η q r (by simpa only [Nat.cast_zero] using hz)⟩
  | succ n ih =>
    have htime : ((n+1:ℕ):ℝ≥0)*δ = (n:ℝ≥0)*δ+δ := by push_cast; ring
    rw [htime]
    intro η q r
    let a : ℝ≥0 := (n:ℝ≥0)*δ
    have ha : a ≤ a+δ := le_add_right le_rfl
    let qs := shifted hW hWm a δ A C η q
    let rs := shifted hW hWm a δ A C η r
    have hfutureClass := local_classes_unique (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
      (fun i ↦ CommonTimeShift.continuous_driver (hWc i) a)
      (CommonShiftRepresentation.pair_shift hpair a) (CommonShiftRepresentation.channels_shift hchannels a)
      i₀ δ A C η qs rs hc
    have hfuture := local_paths_unique (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
      (fun i ↦ CommonTimeShift.continuous_driver (hWc i) a)
      (CommonShiftRepresentation.pair_shift hpair a) (CommonShiftRepresentation.channels_shift hchannels a)
      i₀ δ A C η qs rs hc
    change ∀ᵐ ω ∂μ, ∀ b s, s ≤ δ → q.path b (a+s) ω = r.path b (a+s) ω at hfuture
    have hjoin (b : κ) : q.path b a =ᵐ[μ] r.path b a := by
      filter_upwards [hfuture] with ω hω
      simpa only [add_zero] using hω b 0 zero_le
    let ηq := sectionLp hW hWm (a+δ) A C η q a ha
    let ηr := sectionLp hW hWm (a+δ) A C η r a ha
    have hterminal : ηr = ηq := by
      funext b
      apply Lp.ext
      exact (sectionLp_ae hW hWm (a+δ) A C η r a ha b).trans
        ((hjoin b).symm.trans (sectionLp_ae hW hWm (a+δ) A C η q a ha b).symm)
    let qp := prefixSolution hW hWm i₀ a (a+δ) ha A C η q
    let rp := prefixSolution hW hWm i₀ a (a+δ) ha A C η r
    let rp' := withTerminal hW hWm a A C ηr ηq rp hterminal
    obtain ⟨hpastClass,hpast⟩ := ih ηq qp rp'
    change ∀ᵐ ω ∂μ, ∀ b t, t ≤ a → q.path b t ω = r.path b t ω at hpast
    refine ⟨?_,?_⟩
    · apply Prod.ext
      · funext b
        apply h2_ext hWm i₀ a δ
        · exact congrArg (fun X ↦ X.1 b) hpastClass
        · exact congrArg (fun X ↦ X.1 b) hfutureClass
      · funext b
        apply WithLp.ofLp_injective 2
        funext i
        apply h2_ext hWm i₀ a δ
        · exact congrArg (fun X ↦ X.2 b i) hpastClass
        · exact congrArg (fun X ↦ X.2 b i) hfutureClass
    · filter_upwards [hpast,hfuture] with ω hp hf
      intro b t ht
      by_cases hta : t ≤ a
      · exact hp b t hta
      · have hat : a ≤ t := le_of_not_ge hta
        have hs : t-a ≤ δ := tsub_le_iff_right.mpr (by simpa only [add_comm δ a] using ht)
        simpa only [add_tsub_cancel_of_le hat] using hf b (t-a) hs

/-- For every finite horizon, any two actual backward S²×H² solutions with
identical terminal data have identical state/diffusion classes and paths. -/
theorem global_unique (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) (η : κ → Lp ℝ 2 μ)
    (q r : Solution (𝓕:=𝓕) hW hWm T A C η) :
    q.X = r.X ∧ (∀ᵐ ω ∂μ, ∀ b t, t ≤ T → q.path b t ω = r.path b t ω) := by
  obtain ⟨N,hN,hc⟩ := BSDEGlobalExistence.exists_mesh T A C
  have hne : (N:ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N:ℝ≥0)*(T/(N:ℝ≥0)) = T := mul_div_cancel₀ T hne
  have hh := unique_grid hW hWm hWc hpair hchannels i₀ (T/(N:ℝ≥0)) A C hc N
  rw [he] at hh
  exact hh η q r

end LinearStochastic.BSDEGlobalUniqueness
