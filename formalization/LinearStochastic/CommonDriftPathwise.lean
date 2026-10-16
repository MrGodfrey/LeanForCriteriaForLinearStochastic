/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

The elementary uniform-limit argument below is adapted from the corresponding
Itô modification proof at MathFin 99b836298731c432a6242fdb6cb51c1c97f37902,
using the independently proved deterministic drift maximal estimate instead.
-/
import LinearStochastic.CommonDriftModification
noncomputable section
namespace LinearStochastic.CommonDriftPathwise
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open CommonItoL2 CommonItoCLM CommonItoContinuous CommonDriftPredictable CommonDriftModification
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [CommonItoIsometry.ForwardIndependent B 𝓕 μ]

/-- Consecutive-difference bound combining linearity with the running-max keystone:
for `t ≤ T`, `‖(Vₐ ● B)_t − (Vₐ₊₁ ● B)_t‖` is at most the running max of
`(Vₐ − Vₐ₊₁) ● B` over `[0,T]`. -/
lemma drift_consecutive_norm_le (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (V : ℕ → TBoundedSP (𝓕 := 𝓕) T hBmeas)
    (ω : Ω) {t : ℝ≥0} (ht : t ≤ T) (a : ℕ) :
    ‖driftSimpleProcess hBmeas (V a).val t ω - driftSimpleProcess hBmeas (V (a + 1)).val t ω‖
      ≤ ⨆ j : Set.Iic T, ‖driftSimpleProcess hBmeas (V a - V (a + 1)).val (j : ℝ≥0) ω‖ := by
  have hcoe : ((V a - V (a + 1)).val : SimpleProcess ℝ (𝓕))
      = (V a).val - (V (a + 1)).val := rfl
  rw [show driftSimpleProcess hBmeas (V a).val t ω - driftSimpleProcess hBmeas (V (a + 1)).val t ω
        = driftSimpleProcess hBmeas (V a - V (a + 1)).val t ω from by
      rw [hcoe]; exact (congrFun (driftSimpleProcess_sub hBmeas (V a).val (V (a + 1)).val t) ω).symm]
  simpa only [Real.norm_eq_abs] using drift_norm_le_iSup_Iic hBmeas (V a - V (a + 1)).val ω ht

/-- **Pathwise continuity (the rest of Task 6).** For almost every `ω`, the
pathwise limit `t ↦ driftContinuousMod φ t ω` is continuous on `[0,T]`. The
approximating continuous paths `(Vₙ ● B)_· ω` (B3) converge to it *uniformly* on
`[0,T]`: the running max gives `‖driftContinuousMod φ t ω − (Vₙ ● B)_t ω‖ ≤
4·(3/4)ⁿ` for all `t ≤ T` once `n` is large (geometric tail of the consecutive
differences, uniform in `t`). A uniform limit of continuous functions is
continuous. -/
theorem driftContinuousMod_continuousOn (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ driftContinuousMod T hBmeas φ t ω) (Set.Icc 0 T) := by
  set V := (approxSeq T hBmeas φ).choose with hVdef
  have hV := (approxSeq T hBmeas φ).choose_spec
  filter_upwards [drift_ae_eventually_sup_lt T hBmeas φ V hV,
    driftContinuousMod_tendsto T hBmeas φ] with ω hω htends
  rw [show (Set.Icc 0 T : Set ℝ≥0) = Set.Iic T from by
    ext x; simp only [Set.mem_Icc, Set.mem_Iic, zero_le, true_and]]
  obtain ⟨N, hN⟩ := eventually_atTop.mp hω
  have huniform : TendstoUniformlyOn (fun n t ↦ driftSimpleProcess hBmeas (V n).val t ω)
      (fun t ↦ driftContinuousMod T hBmeas φ t ω) atTop (Set.Iic T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have htend0 : Tendsto (fun n ↦ 4 * (3 / 4 : ℝ) ^ n) atTop (𝓝 0) := by
      rw [show (0 : ℝ) = 4 * 0 from by ring]
      exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul 4
    filter_upwards [eventually_ge_atTop N, htend0.eventually_lt_const hε] with n hn hnε
    intro t ht
    rw [Set.mem_Iic] at ht
    rw [dist_comm]
    -- the uniform bound: dist (fₙ t ω) (X t ω) ≤ 4·(3/4)ⁿ
    have htendsto : Tendsto (fun k ↦ driftSimpleProcess hBmeas (V (k + n)).val t ω) atTop
        (𝓝 (driftContinuousMod T hBmeas φ t ω)) := (htends t ht).comp (tendsto_add_atTop_nat n)
    have hstep : ∀ k, dist (driftSimpleProcess hBmeas (V (k + n)).val t ω)
        (driftSimpleProcess hBmeas (V (k + 1 + n)).val t ω) ≤ (3 / 4 : ℝ) ^ n * (3 / 4 : ℝ) ^ k := by
      intro k
      rw [show k + 1 + n = (k + n) + 1 from by ring, dist_eq_norm]
      refine (drift_consecutive_norm_le T hBmeas V ω ht (k + n)).trans ?_
      simpa only [Real.norm_eq_abs] using (hN (k + n) (hn.trans (Nat.le_add_left n k))).le.trans
        (le_of_eq (by rw [pow_add]; ring))
    have h0 :=
      dist_le_of_le_geometric_of_tendsto₀ (3 / 4) ((3 / 4 : ℝ) ^ n) (by norm_num) hstep htendsto
    simp only [zero_add] at h0
    refine lt_of_le_of_lt (h0.trans (le_of_eq ?_)) hnε
    rw [show (1 : ℝ) - 3 / 4 = 1 / 4 from by norm_num]; ring
  have hcont : ∀ᶠ n in atTop,
      ContinuousOn (fun t ↦ driftSimpleProcess hBmeas (V n).val t ω) (Set.Iic T) :=
    Eventually.of_forall fun n ↦
      (driftSimpleProcess_continuous hBmeas (V n).val ω).continuousOn
  exact huniform.continuousOn hcont.frequently


end LinearStochastic.CommonDriftPathwise
