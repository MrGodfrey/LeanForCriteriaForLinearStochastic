import LinearStochastic.CommonForwardTerminal
import LinearStochastic.CommonGlobalUniqueness
import LinearStochastic.CommonBrownianGlobal

/-! Quantitative dependence of actual forward endpoints on every finite horizon.
A genuine prefix/restart induction propagates the local coefficient bound. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonForwardGlobalBound
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonVectorPicard CommonLocalSolution CommonSolutionData CommonForwardTerminal
open CommonHorizonRestriction CommonSolutionRestriction CommonShiftH2 CommonShiftSimple

/-- Explicit finite iteration of the local endpoint estimate. -/
def meshBound (K : ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => K*(meshBound K n+1)

theorem meshBound_nonneg {K : ℝ} (hK : 0 ≤ K) (n : ℕ) : 0 ≤ meshBound K n := by
  induction n with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg hK (add_nonneg ih zero_le_one)

/-- Coordinatewise linear contractions are contractions for the finite Pi norm. -/
theorem pi_contraction {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {ν : Type*} [Fintype ν]
    (L : E →L[ℝ] F) (hL : ∀ x, ‖L x‖ ≤ ‖x‖) (u v : ν → E) :
    ‖(fun b ↦ L (u b))-(fun b ↦ L (v b))‖ ≤ ‖u-v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro b
  change ‖L (u b)-L (v b)‖ ≤ _
  rw [←map_sub]
  exact (hL _).trans (norm_le_pi_norm (u-v) b)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

omit [Fintype ι] in
theorem restriction_norm (i₀ : ι) {t T : ℝ≥0} (h : t ≤ T) (f : H2 𝓕 μ T) :
    ‖restriction (hWm i₀) h f‖ ≤ ‖f‖ := by
  simp only [Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.memLp f).2.ne
  rw [eLpNorm_congr_ae (restriction_ae (hWm i₀) h f)]
  exact eLpNorm_mono_measure _ (measure_le (hWm i₀) h)

include hWc in
/-- Every actual solution obeys the finite-mesh endpoint estimate. -/
theorem grid_endpoint_difference (i₀ : ι) (δ : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (hb : CommonUniformHorizon.bound δ A C < 1)
    (ξ ζ : κ → Ω → ℝ) (_hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (_hζ : ∀ b, StronglyMeasurable[𝓕 0] (ζ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (hζ2 : ∀ b, MemLp (ζ b) 2 μ) :
    ∀ N : ℕ, ∀ u v : ν → H2 𝓕 μ ((N:ℝ≥0)*δ),
      ∀ (q : Solution hW hWm ((N:ℝ≥0)*δ) A B C D ξ u)
        (r : Solution hW hWm ((N:ℝ≥0)*δ) A B C D ζ v),
        ‖endpoint hW hWm _ A B C D ξ u q-endpoint hW hWm _ A B C D ζ v r‖ ≤
          meshBound (localBound δ A B C D) N *
            (‖(fun b ↦ (hξ2 b).toLp (ξ b))-(fun b ↦ (hζ2 b).toLp (ζ b))‖+‖u-v‖) := by
  intro N
  induction N with
  | zero =>
    intro u v q r
    have hq : endpoint hW hWm _ A B C D ξ u q = fun b ↦ (hξ2 b).toLp (ξ b) := by
      funext b
      apply Lp.ext
      exact (endpoint_memLp hW hWm _ A B C D ξ u q b).2.coeFn_toLp.trans
        (by simpa only [Nat.cast_zero,zero_mul] using (q.initial b).trans (hξ2 b).coeFn_toLp.symm)
    have hr : endpoint hW hWm _ A B C D ζ v r = fun b ↦ (hζ2 b).toLp (ζ b) := by
      funext b
      apply Lp.ext
      exact (endpoint_memLp hW hWm _ A B C D ζ v r b).2.coeFn_toLp.trans
        (by simpa only [Nat.cast_zero,zero_mul] using (r.initial b).trans (hζ2 b).coeFn_toLp.symm)
    rw [hq,hr]
    simp only [meshBound,one_mul]
    exact le_add_of_nonneg_right (norm_nonneg _)
  | succ n ih =>
    have htime : ((n+1:ℕ):ℝ≥0)*δ = (n:ℝ≥0)*δ+δ := by push_cast; ring
    rw [htime]
    intro u v q r
    let a : ℝ≥0 := (n:ℝ≥0)*δ
    have ha : a ≤ a+δ := le_add_right le_rfl
    let qp := prefixSolution hW hWm i₀ a (a+δ) ha A B C D ξ u q
    let rp := prefixSolution hW hWm i₀ a (a+δ) ha A B C D ζ v r
    let up := fun b ↦ restriction (hWm i₀) ha (u b)
    let vp := fun b ↦ restriction (hWm i₀) ha (v b)
    have hpast := ih up vp qp rp
    have hpre : ‖up-vp‖ ≤ ‖u-v‖ :=
      pi_contraction (restriction (hWm i₀) ha) (restriction_norm hWm i₀ ha) u v
    have hK := (one_le_localBound δ A B C D hb).trans' zero_le_one
    have hN := meshBound_nonneg hK n
    have hpast' := hpast.trans (mul_le_mul_of_nonneg_left (add_le_add_right hpre _) hN)
    let qs := shifted hW hWm a δ (a+δ) le_rfl A B C D ξ u q
    let rs := shifted hW hWm a δ (a+δ) le_rfl A B C D ζ v r
    have hF0 : 𝓕 a ≤ CommonTimeShift.filtration 𝓕 a 0 := by
      change 𝓕 a ≤ 𝓕 (a+0)
      rw [add_zero]
    have hstart (b : κ) : StronglyMeasurable[CommonTimeShift.filtration 𝓕 a 0] (q.path b a) :=
      ((q.progressive b).isStronglyProgressive.stronglyAdapted a).mono hF0
    have hend (b : κ) : StronglyMeasurable[CommonTimeShift.filtration 𝓕 a 0] (r.path b a) :=
      ((r.progressive b).isStronglyProgressive.stronglyAdapted a).mono hF0
    have hstart2 (b : κ) : MemLp (q.path b a) 2 μ :=
      (endpoint_memLp hW hWm a A B C D ξ up qp b).2
    have hend2 (b : κ) : MemLp (r.path b a) 2 μ :=
      (endpoint_memLp hW hWm a A B C D ζ vp rp b).2
    have hfuture := local_endpoint_difference (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
      (fun i ↦ CommonTimeShift.continuous_driver (hWc i) a) i₀ δ A B C D
      (fun b ↦ q.path b a) (fun b ↦ r.path b a) hstart hend hstart2 hend2
      (fun b ↦ shiftCLM a δ (a+δ) le_rfl (u b))
      (fun b ↦ shiftCLM a δ (a+δ) le_rfl (v b)) qs rs hb
    have hshift := pi_contraction (shiftCLM (𝓕:=𝓕) (μ:=μ) a δ (a+δ) le_rfl)
      (shift_norm a δ (a+δ) le_rfl) u v
    change ‖endpoint hW hWm (a+δ) A B C D ξ u q-endpoint hW hWm (a+δ) A B C D ζ v r‖ ≤
      localBound δ A B C D *
        (‖endpoint hW hWm a A B C D ξ up qp-endpoint hW hWm a A B C D ζ vp rp‖+
          ‖(fun b ↦ shiftCLM a δ (a+δ) le_rfl (u b))-(fun b ↦ shiftCLM a δ (a+δ) le_rfl (v b))‖) at hfuture
    have hh := hfuture.trans (mul_le_mul_of_nonneg_left (add_le_add hpast' hshift) hK)
    apply hh.trans
    change localBound δ A B C D *
      (meshBound (localBound δ A B C D) n *
        (‖(fun b ↦ (hξ2 b).toLp (ξ b))-(fun b ↦ (hζ2 b).toLp (ζ b))‖+‖u-v‖)+‖u-v‖) ≤ _
    rw [meshBound]
    have hi := norm_nonneg ((fun b ↦ (hξ2 b).toLp (ξ b))-(fun b ↦ (hζ2 b).toLp (ζ b)))
    nlinarith [mul_nonneg hK hi]

include hWc in
/-- On each finite horizon a finite coefficient-only constant controls genuine
terminal differences for every pair of actual solutions and controls. -/
theorem endpoint_continuous_dependence (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ ζ : κ → Ω → ℝ)
      (_hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b)) (_hζ : ∀ b, StronglyMeasurable[𝓕 0] (ζ b))
      (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (hζ2 : ∀ b, MemLp (ζ b) 2 μ)
      (u v : ν → H2 𝓕 μ T) (q : Solution hW hWm T A B C D ξ u)
      (r : Solution hW hWm T A B C D ζ v),
      ‖endpoint hW hWm T A B C D ξ u q-endpoint hW hWm T A B C D ζ v r‖ ≤
        K*(‖(fun b ↦ (hξ2 b).toLp (ξ b))-(fun b ↦ (hζ2 b).toLp (ζ b))‖+‖u-v‖) := by
  obtain ⟨N,hN,hb⟩ := CommonUniformHorizon.exists_mesh T A C
  let δ := T/(N:ℝ≥0)
  have hne : (N:ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N:ℝ≥0)*δ = T := mul_div_cancel₀ T hne
  refine ⟨meshBound (localBound δ A B C D) N,
    meshBound_nonneg ((one_le_localBound δ A B C D hb).trans' zero_le_one) N,?_⟩
  intro ξ ζ hξ hζ hξ2 hζ2
  have hh := grid_endpoint_difference hW hWm hWc i₀ δ A B C D hb ξ ζ hξ hζ hξ2 hζ2 N
  rw [he] at hh
  exact hh
/-- The same actual global estimate for original Brownian drivers with merely
almost-sure continuous paths. Genuine driver-version transport leaves both
control and endpoint unchanged on the original probability space. -/
theorem brownian_endpoint_continuous_dependence [𝓕.IsComplete μ]
    (hB : ∀ i, IsBrownianReal (W i) μ) (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ξ ζ : κ → Ω → ℝ)
      (_hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b)) (_hζ : ∀ b, StronglyMeasurable[𝓕 0] (ζ b))
      (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (hζ2 : ∀ b, MemLp (ζ b) 2 μ)
      (u v : ν → H2 𝓕 μ T)
      (q : Solution (fun i ↦ (hB i).toIsPreBrownianReal) hWm T A B C D ξ u)
      (r : Solution (fun i ↦ (hB i).toIsPreBrownianReal) hWm T A B C D ζ v),
      ‖endpoint (fun i ↦ (hB i).toIsPreBrownianReal) hWm T A B C D ξ u q-
        endpoint (fun i ↦ (hB i).toIsPreBrownianReal) hWm T A B C D ζ v r‖ ≤
        K*(‖(fun b ↦ (hξ2 b).toLp (ξ b))-(fun b ↦ (hζ2 b).toLp (ζ b))‖+‖u-v‖) := by
  obtain ⟨K,hK,hbound⟩ := endpoint_continuous_dependence (𝓕:=𝓕)
    (fun i ↦ (CommonBrownianRepair.repaired_brownian hB i).toIsPreBrownianReal)
    (CommonBrownianRepair.repaired_measurable hB) (CommonBrownianRepair.repaired_continuous hB)
    i₀ T A B C D
  refine ⟨K,hK,?_⟩
  intro ξ ζ hξ hζ hξ2 hζ2 u v q r
  have he (i : ι) : ∀ᵐ ω ∂μ, ∀ t, W i t ω = CommonBrownianRepair.repaired hB i t ω :=
    (hB i).mk_ae_forall_eq.mono (fun _ hω t ↦ (hω t).symm)
  let q' := CommonBrownianGlobal.change_driver (fun i ↦ (hB i).toIsPreBrownianReal)
    (fun i ↦ (CommonBrownianRepair.repaired_brownian hB i).toIsPreBrownianReal)
    hWm (CommonBrownianRepair.repaired_measurable hB) he T A B C D ξ u q
  let r' := CommonBrownianGlobal.change_driver (fun i ↦ (hB i).toIsPreBrownianReal)
    (fun i ↦ (CommonBrownianRepair.repaired_brownian hB i).toIsPreBrownianReal)
    hWm (CommonBrownianRepair.repaired_measurable hB) he T A B C D ζ v r
  exact hbound ξ ζ hξ hζ hξ2 hζ2 u v q' r'
end LinearStochastic.CommonForwardGlobalBound
