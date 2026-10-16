import LinearStochastic.BSDEPathPaste
import LinearStochastic.CommonShiftRepresentation

/-! Genuine arbitrary finite-horizon backward construction by a finite reverse
mesh. Representation is an explicit input here and will be discharged for the
actual usual Brownian filtration in a separate specialization. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BSDEGlobalExistence
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard BSDEMatrixPicard BSDEPathData
open CommonTimeShift CommonShiftSimple
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  {ι κ : Type*} [Fintype ι] [Fintype κ]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

/-- The literal backward contraction rate is monotone in the horizon. -/
theorem rate_mono (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) :
    Monotone (fun T ↦ BSDEMatrixPicard.rate T A C) := by
  intro s t h
  exact mul_le_mul_of_nonneg_right
    (add_le_add (mul_le_mul_of_nonneg_right (show (s:ℝ) ≤ t from h) (by positivity))
      (Real.sqrt_le_sqrt h)) (coefficientSize_nonneg A C)

/-- Every finite horizon has a genuine finite mesh satisfying the backward
Picard contraction estimate. -/
theorem exists_mesh (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) :
    ∃ N : ℕ, 0 < N ∧ BSDEMatrixPicard.rate (T / (N:ℝ≥0)) A C < 1 := by
  obtain ⟨δ,hδ,hb⟩ := exists_positive_contraction_horizon A C
  obtain ⟨n,hn⟩ := exists_nat_gt ((T:ℝ)/(δ:ℝ))
  refine ⟨n+1,Nat.succ_pos n,?_⟩
  have hd : 0 < (δ:ℝ) := hδ
  have hT : (T:ℝ) < (n:ℝ)*δ := (div_lt_iff₀ hd).mp hn
  have hm : T / ((n+1:ℕ):ℝ≥0) ≤ δ := by
    apply (div_le_iff₀ (by positivity)).mpr
    exact_mod_cast (show (T:ℝ) ≤ (δ:ℝ)*((n:ℝ)+1) by nlinarith)
  exact (rate_mono A C hm).trans_lt hb

include hWc hpair hchannels

/-- Genuine finite reverse induction. The shifted representation retains all
of the original information at the joining time. -/
theorem exists_grid (i₀ : ι) (δ : ℝ≥0) (hδ : 0 < δ)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (hc : BSDEMatrixPicard.rate δ A C < 1)
    (hMR : ∀ T (χ : Lp ℝ 2 μ), AEStronglyMeasurable[𝓕 T] χ μ →
      BSDEIntegralRange.Represented hW hWm hpair hchannels T χ) :
    ∀ N : ℕ, ∀ η : κ → Lp ℝ 2 μ,
      (∀ b, AEStronglyMeasurable[𝓕 ((N:ℝ≥0)*δ)] (η b) μ) →
      Nonempty (Solution (𝓕:=𝓕) hW hWm ((N:ℝ≥0)*δ) A C η) := by
  intro N
  induction N with
  | zero =>
    intro η hη
    have hr : BSDEMatrixPicard.rate (((0:ℕ):ℝ≥0)*δ) A C < 1 := by simp [BSDEMatrixPicard.rate]
    exact BSDEPathData.exists_local hW hWm hWc hpair hchannels i₀ _ A C η hη (hMR _) hr
  | succ n ih =>
    have htime : ((n+1:ℕ):ℝ≥0)*δ = (n:ℝ≥0)*δ+δ := by push_cast; ring
    rw [htime]
    intro η hη
    let a : ℝ≥0 := (n:ℝ≥0)*δ
    have hmrs (χ : Lp ℝ 2 μ) (hχ : AEStronglyMeasurable[filtration 𝓕 a δ] χ μ) :
        BSDEIntegralRange.Represented (𝓕:=filtration 𝓕 a)
          (fun i ↦ preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
          (CommonShiftRepresentation.pair_shift hpair a)
          (CommonShiftRepresentation.channels_shift hchannels a) δ χ :=
      CommonShiftRepresentation.represented_shift hW hWm hpair hchannels a δ χ
        (hMR (a+δ) χ hχ)
    obtain ⟨r⟩ := BSDEPathData.exists_local (𝓕:=filtration 𝓕 a)
      (fun i ↦ preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
      (fun i ↦ continuous_driver (hWc i) a)
      (CommonShiftRepresentation.pair_shift hpair a)
      (CommonShiftRepresentation.channels_shift hchannels a) i₀ δ A C η hη hmrs hc
    have hstart (b : κ) := section_memLp (𝓕:=filtration 𝓕 a)
      (fun i ↦ preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
      δ A C η r b 0 bot_le
    let η₀ : κ → Lp ℝ 2 μ := fun b ↦ (hstart b).2.toLp (r.path b 0)
    have hη₀ (b : κ) : AEStronglyMeasurable[𝓕 a] (η₀ b) μ := by
      have hm : StronglyMeasurable[𝓕 a] (r.path b 0) := by
        apply (hstart b).1.mono
        change 𝓕 (a+0) ≤ 𝓕 a
        rw [add_zero]
      exact hm.aestronglyMeasurable.congr ((hstart b).2.coeFn_toLp).symm
    obtain ⟨q⟩ := ih η₀ hη₀
    have he (b : κ) : q.path b a =ᵐ[μ] r.path b 0 :=
      (q.terminal b).trans ((hstart b).2.coeFn_toLp)
    exact BSDEPathPaste.exists_paste hW hWm i₀ a δ hδ A C η₀ η q r he

/-- Arbitrary positive-horizon actual backward existence, with a continuous S²
state, genuine predictable H² diffusion and the literal coefficient equation. -/
theorem exists_global (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (hη : ∀ b, AEStronglyMeasurable[𝓕 T] (η b) μ)
    (hMR : ∀ t (χ : Lp ℝ 2 μ), AEStronglyMeasurable[𝓕 t] χ μ →
      BSDEIntegralRange.Represented hW hWm hpair hchannels t χ) :
    Nonempty (Solution (𝓕:=𝓕) hW hWm T A C η) := by
  obtain ⟨N,hN,hc⟩ := exists_mesh T A C
  have hNpos : (0:ℝ≥0) < N := by exact_mod_cast hN
  have hδ : 0 < T/(N:ℝ≥0) := div_pos hT hNpos
  have he : (N:ℝ≥0)*(T/(N:ℝ≥0)) = T := mul_div_cancel₀ T (ne_of_gt hNpos)
  have hh := exists_grid hW hWm hWc hpair hchannels i₀ (T/(N:ℝ≥0)) hδ A C hc hMR N
  rw [he] at hh
  exact hh η hη

end LinearStochastic.BSDEGlobalExistence
