module

public import LinearStochastic.BSDEProcessLift
public import LinearStochastic.CommonPicardHorizon

@[expose] public section

/-! The literal finite-dimensional adjoint BSDE iteration. This constructs the
actual predictable H² fixed point. Its terminal identification still requires
martingale representation and is deliberately not asserted by this module. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BSDEMatrixPicard
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open CommonItoMultichannel CommonVectorPicard BSDEIntegralRange BSDEProcessLift
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ : Type*} [Fintype ι] [Fintype κ]

abbrev PairH2 (T : ℝ≥0) :=
  (κ → H2 𝓕 μ T) × (κ → ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T)

/-- The actual coordinate driver AᵀY + ∑ CᵢᵀZᵢ of the adjoint BSDE. -/
def driver (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) : κ → H2 𝓕 μ T :=
  matrixAction T A.transpose X.1 + ∑ i, matrixAction T (C i).transpose (fun a ↦ X.2 a i)

omit [IsProbabilityMeasure μ] in
theorem driver_apply (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) (a : κ) :
    driver T A C X a = (∑ b, A b a • X.1 b) + ∑ i, ∑ b, C i b a • X.2 b i := by
  simp only [driver, Pi.add_apply, CommonVectorPicard.matrixAction_apply,
    Matrix.transpose_apply, Finset.sum_apply]

omit [IsProbabilityMeasure μ] in
theorem driver_sub (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (X Y : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    driver T A C (X-Y) = driver T A C X - driver T A C Y := by
  funext a
  simp only [driver_apply, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, PiLp.sub_apply,
    smul_sub, Finset.sum_sub_distrib]
  abel

/-- A genuine uniform bound in literal entries, independent of the horizon. -/
def coefficientSize (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) : ℝ :=
  CommonPicardHorizon.matrixSize A.transpose + ∑ i, CommonPicardHorizon.matrixSize (C i).transpose

theorem coefficientSize_nonneg (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) :
    0 ≤ coefficientSize A C := by
  exact add_nonneg (CommonPicardHorizon.matrixSize_nonneg _)
    (Finset.sum_nonneg fun i _ ↦ CommonPicardHorizon.matrixSize_nonneg _)

omit [IsProbabilityMeasure μ] in
theorem channel_norm_le (T : ℝ≥0)
    (X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) (i : ι) :
    ‖fun a ↦ X.2 a i‖ ≤ ‖X‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg X)).mpr
  intro a
  exact (PiLp.norm_apply_le (X.2 a) i).trans ((norm_le_pi_norm X.2 a).trans (norm_snd_le X))

omit [IsProbabilityMeasure μ] in
theorem driver_norm_le (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    ‖driver T A C X‖ ≤ coefficientSize A C * ‖X‖ := by
  have hm (M : Matrix κ κ ℝ) (Y : κ → H2 𝓕 μ T) :
      ‖matrixAction T M Y‖ ≤ CommonPicardHorizon.matrixSize M * ‖Y‖ :=
    ((matrixAction T M).le_opNorm Y).trans (mul_le_mul_of_nonneg_right
      (CommonPicardHorizon.matrixAction_norm_le T M) (norm_nonneg Y))
  calc
    _ ≤ ‖matrixAction T A.transpose X.1‖ +
        ‖∑ i, matrixAction T (C i).transpose (fun a ↦ X.2 a i)‖ := norm_add_le _ _
    _ ≤ CommonPicardHorizon.matrixSize A.transpose * ‖X.1‖ +
        ∑ i, CommonPicardHorizon.matrixSize (C i).transpose * ‖fun a ↦ X.2 a i‖ :=
      add_le_add (hm _ _) ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ hm _ _))
    _ ≤ CommonPicardHorizon.matrixSize A.transpose * ‖X‖ +
        ∑ i, CommonPicardHorizon.matrixSize (C i).transpose * ‖X‖ := by
      exact add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le X) (CommonPicardHorizon.matrixSize_nonneg _))
        (Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (channel_norm_le T X i)
          (CommonPicardHorizon.matrixSize_nonneg _))
    _ = _ := by rw [← Finset.sum_mul, ← add_mul]; rfl

omit [IsProbabilityMeasure μ] in
theorem driver_difference (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (X Y : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    ‖driver T A C X - driver T A C Y‖ ≤ coefficientSize A C * ‖X-Y‖ := by
  rw [← driver_sub]
  exact driver_norm_le T A C (X-Y)

/-- Explicit backward contraction rate for the actual product of predictable
state and diffusion spaces. -/
def rate (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) : ℝ :=
  ((T : ℝ) * (2 + Fintype.card ι) + Real.sqrt (T : ℝ)) * coefficientSize A C

theorem rate_nonneg (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) :
    0 ≤ rate T A C := by unfold rate; exact mul_nonneg (by positivity) (coefficientSize_nonneg A C)

variable {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

/-- The actual terminal-input, conditional-projection and Itô-adjoint iteration. -/
def picardMap (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T :=
  (fun a ↦ stateStep hW hWm hWc hpair hchannels i₀ T (η a) (driver T A C X a),
   fun a ↦ diffusionStep hW hWm hpair hchannels T (η a) (driver T A C X a))

theorem picardMap_contraction (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (X Y : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    ‖picardMap hW hWm hWc hpair hchannels i₀ T A C η X -
      picardMap hW hWm hWc hpair hchannels i₀ T A C η Y‖ ≤ rate T A C * ‖X-Y‖ := by
  have hr : 0 ≤ rate T A C * ‖X-Y‖ := mul_nonneg (rate_nonneg T A C) (norm_nonneg _)
  have hd (a : κ) : ‖driver T A C X a - driver T A C Y a‖ ≤ coefficientSize A C * ‖X-Y‖ :=
    (norm_le_pi_norm (driver T A C X - driver T A C Y) a).trans (driver_difference T A C X Y)
  rw [Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro a
    calc
      _ ≤ (T : ℝ)*(2+Fintype.card ι)*‖driver T A C X a - driver T A C Y a‖ :=
        stateStep_difference hW hWm hWc hpair hchannels i₀ T (η a) _ _
      _ ≤ (T : ℝ)*(2+Fintype.card ι)*(coefficientSize A C*‖X-Y‖) :=
        mul_le_mul_of_nonneg_left (hd a) (by positivity)
      _ ≤ rate T A C*‖X-Y‖ := by
        unfold rate
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (coefficientSize_nonneg A C)) (norm_nonneg _)
  · apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro a
    calc
      _ ≤ Real.sqrt (T:ℝ)*‖driver T A C X a - driver T A C Y a‖ :=
        diffusionStep_difference hW hWm hpair hchannels T (η a) _ _
      _ ≤ Real.sqrt (T:ℝ)*(coefficientSize A C*‖X-Y‖) :=
        mul_le_mul_of_nonneg_left (hd a) (Real.sqrt_nonneg _)
      _ ≤ rate T A C*‖X-Y‖ := by
        unfold rate
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (by positivity)) (coefficientSize_nonneg A C)) (norm_nonneg _)

theorem exists_unique_fixedPoint (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (hc : rate T A C < 1) :
    ∃! X, picardMap hW hWm hWc hpair hchannels i₀ T A C η X = X := by
  letI : CompleteSpace (PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) := by
    unfold PairH2 H2
    infer_instance
  have hr := rate_nonneg T A C
  have hcontract : ContractingWith (Real.toNNReal (rate T A C))
      (picardMap hW hWm hWc hpair hchannels i₀ T A C η) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun X Y ↦ ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr, NNReal.coe_one]
      exact hc
    · rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hr]
      exact picardMap_contraction hW hWm hWc hpair hchannels i₀ T A C η X Y
  exact ⟨hcontract.fixedPoint _, hcontract.fixedPoint_isFixedPt,
    fun Y hY ↦ hcontract.fixedPoint_unique hY⟩

/-- Every literal finite matrix adjoint system admits a positive backward
contraction horizon; the bound uses only absolute coefficient entries. -/
theorem exists_positive_contraction_horizon (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) :
    ∃ T : ℝ≥0, 0 < T ∧ rate T A C < 1 := by
  let K := coefficientSize A C
  let d : ℝ := 3 + Fintype.card ι
  have hK : 0 ≤ K := coefficientSize_nonneg A C
  have hd : 0 < d := by dsimp [d]; positivity
  let h : ℝ := 1 / (2 * (K+1) * d)
  have hpos : 0 < h := by dsimp [h]; positivity
  have hle : h ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*(K+1)*d)).mpr
    have hd3 : 3 ≤ d := by dsimp [d]; exact le_add_of_nonneg_right (Nat.cast_nonneg _)
    nlinarith
  have hmul : h * ((K+1)*d) = 1/2 := by
    dsimp [h]
    field_simp
  let T : ℝ≥0 := ⟨h^2,sq_nonneg h⟩
  refine ⟨T, by change 0 < h^2; positivity, ?_⟩
  have hroot : Real.sqrt (T:ℝ) = h := Real.sqrt_sq hpos.le
  have hT : (T:ℝ) ≤ h := by change h^2 ≤ h; nlinarith
  have hfac : (T:ℝ)*(2+Fintype.card ι)+Real.sqrt (T:ℝ) ≤ h*d := by
    rw [hroot]
    have hh := mul_le_mul_of_nonneg_right hT (by positivity : (0:ℝ) ≤ 2+Fintype.card ι)
    dsimp [d]
    nlinarith
  have hr : rate T A C ≤ h*d*K := by
    exact mul_le_mul_of_nonneg_right hfac hK
  have hstrict : h*d*K < 1 := by nlinarith [mul_pos hpos hd]
  exact hr.trans_lt hstrict

end LinearStochastic.BSDEMatrixPicard
