module

public import LinearStochastic.BSDELocal

@[expose] public section

/-! Explicit terminal-data continuity of the actual backward Picard solution.
The norms are the genuine predictable coordinate H² / Hilbert channel norms. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BSDELocalBounds
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open CommonItoMultichannel CommonVectorPicard BSDEIntegralRange BSDEProcessLift BSDEMatrixPicard
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ : Type*} [Fintype ι] [Fintype κ]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

theorem stateStep_terminal_difference (i₀ : ι) (T : ℝ≥0) (η ψ : Lp ℝ 2 μ) (f : H2 𝓕 μ T) :
    ‖stateStep hW hWm hWc hpair hchannels i₀ T η f - stateStep hW hWm hWc hpair hchannels i₀ T ψ f‖ ≤
      Real.sqrt (T:ℝ)*(1+Fintype.card ι)*‖η-ψ‖ := by
  have he : stateStep hW hWm hWc hpair hchannels i₀ T η f - stateStep hW hWm hWc hpair hchannels i₀ T ψ f =
      assembled hW hWm hWc hpair hchannels T (η-ψ) := by
    rw [stateStep,stateStep,sub_sub_sub_cancel_right,← assembled_sub]
    congr 1
    unfold terminalInput
    abel
  rw [he]
  exact assembled_norm hW hWm hWc hpair hchannels T _

theorem diffusionStep_terminal_difference (T : ℝ≥0) (η ψ : Lp ℝ 2 μ) (f : H2 𝓕 μ T) :
    ‖diffusionStep hW hWm hpair hchannels T η f - diffusionStep hW hWm hpair hchannels T ψ f‖ ≤ ‖η-ψ‖ := by
  have he : diffusionStep hW hWm hpair hchannels T η f - diffusionStep hW hWm hpair hchannels T ψ f =
      coefficients hW hWm hpair hchannels T (η-ψ) := by
    simp only [diffusionStep,terminalInput,map_add,map_sub]
    abel
  rw [he]
  exact coefficients_norm hW hWm hpair hchannels T _

/-- A concrete positive terminal-input bound, uniform over the trial solution. -/
def terminalBound (ι : Type*) [Fintype ι] (T : ℝ≥0) : ℝ :=
  Real.sqrt (T:ℝ)*(1+Fintype.card ι)+1

theorem terminalBound_nonneg (T : ℝ≥0) : 0 ≤ terminalBound ι T := by unfold terminalBound; positivity

theorem picardMap_terminal_difference (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η ψ : κ → Lp ℝ 2 μ) (X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    ‖BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C η X -
      BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C ψ X‖ ≤ terminalBound ι T * ‖η-ψ‖ := by
  have hr := mul_nonneg (terminalBound_nonneg (ι:=ι) T) (norm_nonneg (η-ψ))
  rw [Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro a
    calc
      _ ≤ Real.sqrt (T:ℝ)*(1+Fintype.card ι)*‖η a-ψ a‖ :=
        stateStep_terminal_difference hW hWm hWc hpair hchannels i₀ T _ _ _
      _ ≤ Real.sqrt (T:ℝ)*(1+Fintype.card ι)*‖η-ψ‖ :=
        mul_le_mul_of_nonneg_left (norm_le_pi_norm (η-ψ) a) (by positivity)
      _ ≤ terminalBound ι T*‖η-ψ‖ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
  · apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro a
    calc
      _ ≤ ‖η a-ψ a‖ := diffusionStep_terminal_difference hW hWm hpair hchannels T _ _ _
      _ ≤ ‖η-ψ‖ := norm_le_pi_norm (η-ψ) a
      _ ≤ terminalBound ι T*‖η-ψ‖ := by
        nth_rw 1 [← one_mul ‖η-ψ‖]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (norm_nonneg _)

/-- Actual backward fixed-point state and diffusion depend continuously on the
terminal variable, with explicit coefficient-dependent finite constant. -/
theorem fixedPoint_difference (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η ψ : κ → Lp ℝ 2 μ) (X Y : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T)
    (hc : BSDEMatrixPicard.rate T A C < 1)
    (hX : BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C η X = X)
    (hY : BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C ψ Y = Y) :
    ‖X-Y‖ ≤ (terminalBound ι T * ‖η-ψ‖) / (1-BSDEMatrixPicard.rate T A C) := by
  have hh : ‖X-Y‖ ≤ BSDEMatrixPicard.rate T A C * ‖X-Y‖ + terminalBound ι T * ‖η-ψ‖ := by
    calc
      _ = ‖BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C η X -
        BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C ψ Y‖ := by rw [hX,hY]
      _ ≤ ‖BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C η X -
          BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C η Y‖ +
        ‖BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C η Y -
          BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C ψ Y‖ := by simpa only [dist_eq_norm] using (dist_triangle
          (BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C η X)
          (BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C η Y)
          (BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C ψ Y))
      _ ≤ _ := add_le_add
        (BSDEMatrixPicard.picardMap_contraction hW hWm hWc hpair hchannels i₀ T A C η X Y)
        (picardMap_terminal_difference hW hWm hWc hpair hchannels i₀ T A C η ψ Y)
  apply (le_div_iff₀ (sub_pos.mpr hc)).mpr
  nlinarith

end LinearStochastic.BSDELocalBounds
