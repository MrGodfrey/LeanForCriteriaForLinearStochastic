import LinearStochastic.CommonDriftPredictable
import LinearStochastic.CommonItoMultichannel
import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option maxHeartbeats 1000000

/-!
# Actual short-horizon matrix Picard equation in predictable H²

The state consists of finitely many scalar predictable L² coordinates. Matrix
coefficients act by their literal row sums. The drift and stochastic terms are
the previously constructed continuous extensions of elementary integrals.
This file proves the unique H² fixed point under an explicit short-time bound;
continuous S² realization, an initial-random-variable embedding and global
concatenation are separate statements, not claimed by this fixed point alone.
-/
noncomputable section
namespace LinearStochastic.CommonVectorPicard
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open CommonItoMultichannel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {𝓕 : Filtration ℝ≥0 mΩ}

abbrev H2 (𝓕 : Filtration ℝ≥0 mΩ) (μ : Measure Ω) (T : ℝ≥0) :=
  Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)

/-- The actual finite matrix action on predictable coordinate processes. -/
def matrixAction {κ ν : Type*} [Fintype κ] [Fintype ν]
    (T : ℝ≥0) (A : Matrix κ ν ℝ) :
    (ν → H2 𝓕 μ T) →L[ℝ] (κ → H2 𝓕 μ T) :=
  ContinuousLinearMap.pi fun a ↦ ∑ b, A a b • ContinuousLinearMap.proj b

omit [IsProbabilityMeasure μ] in
@[simp] theorem matrixAction_apply {κ ν : Type*} [Fintype κ] [Fintype ν]
    (T : ℝ≥0) (A : Matrix κ ν ℝ) (X : ν → H2 𝓕 μ T) (a : κ) :
    matrixAction T A X a = ∑ b, A a b • X b := by
  simp only [matrixAction, ContinuousLinearMap.pi_apply, sum_apply,
    smul_apply, ContinuousLinearMap.proj_apply]

variable {ι : Type*} [Fintype ι] {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

/-- Coordinatewise actual deterministic drift integral; the driver index only
selects the existing common-domain presentation and is not used in its increments. -/
def driftVector {κ : Type*} [Fintype κ] (i₀ : ι) (T : ℝ≥0) :
    (κ → H2 𝓕 μ T) →L[ℝ] (κ → H2 𝓕 μ T) :=
  ContinuousLinearMap.pi fun a ↦
    (CommonDriftPredictable.driftProcessAssembled (𝓕:=𝓕) T (hWm i₀)).comp
      (ContinuousLinearMap.proj a)

omit [Fintype ι] in
theorem driftVector_norm_le {κ : Type*} [Fintype κ] (i₀ : ι) (T : ℝ≥0)
    (X : κ → H2 𝓕 μ T) : ‖driftVector hWm i₀ T X‖ ≤ (T : ℝ) * ‖X‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg T.coe_nonneg (norm_nonneg X))).mpr
  intro a
  exact (CommonDriftPredictable.driftProcessAssembled_norm_le T (hWm i₀) (X a)).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm X a) T.coe_nonneg)

/-- The actual Itô process assembled in predictable H², one Brownian channel
at a time and one literal state coordinate at a time. -/
def itoVector {κ : Type*} [Fintype κ] (i : ι) (T : ℝ≥0)
    (X : κ → H2 𝓕 μ T) : κ → H2 𝓕 μ T :=
  fun a ↦ CommonItoPredictable.itoProcessAssembled (hW i) T (hWm i) (hWc i) (X a)

omit [Fintype ι] in
theorem itoVector_add {κ : Type*} [Fintype κ] (i : ι) (T : ℝ≥0)
    (X Y : κ → H2 𝓕 μ T) :
    itoVector hW hWm hWc i T (X+Y) = itoVector hW hWm hWc i T X + itoVector hW hWm hWc i T Y := by
  funext a
  exact CommonItoPredictable.itoProcessAssembled_add (hW i) T (hWm i) (hWc i) (X a) (Y a)

omit [Fintype ι] in
theorem itoVector_sub {κ : Type*} [Fintype κ] (i : ι) (T : ℝ≥0)
    (X Y : κ → H2 𝓕 μ T) :
    itoVector hW hWm hWc i T (X-Y) = itoVector hW hWm hWc i T X - itoVector hW hWm hWc i T Y := by
  funext a
  exact CommonItoPredictable.itoProcessAssembled_sub (hW i) T (hWm i) (hWc i) (X a) (Y a)

omit [Fintype ι] in
theorem itoVector_norm_le {κ : Type*} [Fintype κ] (i : ι) (T : ℝ≥0)
    (X : κ → H2 𝓕 μ T) : ‖itoVector hW hWm hWc i T X‖ ≤ Real.sqrt (T : ℝ) * ‖X‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg X))).mpr
  intro a
  exact (CommonItoPredictable.itoProcessAssembled_norm_le (hW i) T (hWm i) (hWc i) (X a)).trans
    (mul_le_mul_of_nonneg_left (norm_le_pi_norm X a) (Real.sqrt_nonneg _))

variable {κ ν : Type*} [Fintype κ] [Fintype ν]

def picardMap (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (η : κ → H2 𝓕 μ T) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T) : κ → H2 𝓕 μ T :=
  η + driftVector hWm i₀ T (matrixAction T A X + matrixAction T B u) +
    ∑ i, itoVector hW hWm hWc i T (matrixAction T (C i) X + matrixAction T (D i) u)

/-- A genuine coefficient-dependent contraction constant in the finite-coordinate
H² norm, with no assumption about the unknown solution. -/
def rate (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) : ℝ :=
  (T : ℝ) * ‖matrixAction (𝓕:=𝓕) (μ:=μ) T A‖ +
    Real.sqrt (T : ℝ) * ∑ i, ‖matrixAction (𝓕:=𝓕) (μ:=μ) T (C i)‖

omit [IsProbabilityMeasure μ] in
theorem rate_nonneg (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) :
    0 ≤ rate (𝓕:=𝓕) (μ:=μ) T A C := by unfold rate; positivity

theorem picardMap_contraction (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (η X Y : κ → H2 𝓕 μ T) (u : ν → H2 𝓕 μ T) :
    ‖picardMap hW hWm hWc i₀ T A B C D η u X - picardMap hW hWm hWc i₀ T A B C D η u Y‖ ≤
      rate (𝓕:=𝓕) (μ:=μ) T A C * ‖X-Y‖ := by
  have hd : picardMap hW hWm hWc i₀ T A B C D η u X - picardMap hW hWm hWc i₀ T A B C D η u Y =
      driftVector hWm i₀ T (matrixAction T A (X-Y)) +
        ∑ i, itoVector hW hWm hWc i T (matrixAction T (C i) (X-Y)) := by
    simp only [picardMap, map_add, map_sub, itoVector_add, itoVector_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    abel
  rw [hd]
  calc
    _ ≤ ‖driftVector hWm i₀ T (matrixAction T A (X-Y))‖ +
        ‖∑ i, itoVector hW hWm hWc i T (matrixAction T (C i) (X-Y))‖ := norm_add_le _ _
    _ ≤ (T : ℝ) * ‖matrixAction T A (X-Y)‖ +
        ∑ i, Real.sqrt (T : ℝ) * ‖matrixAction T (C i) (X-Y)‖ :=
      add_le_add (driftVector_norm_le hWm i₀ T _)
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ itoVector_norm_le hW hWm hWc i T _))
    _ ≤ (T : ℝ) * (‖matrixAction (𝓕:=𝓕) (μ:=μ) T A‖ * ‖X-Y‖) +
        ∑ i, Real.sqrt (T : ℝ) * (‖matrixAction (𝓕:=𝓕) (μ:=μ) T (C i)‖ * ‖X-Y‖) :=
      add_le_add (mul_le_mul_of_nonneg_left ((matrixAction T A).le_opNorm _) T.coe_nonneg)
        (Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left ((matrixAction T (C i)).le_opNorm _)
          (Real.sqrt_nonneg _))
    _ = _ := by simp only [rate, ← Finset.mul_sum, ← Finset.sum_mul]; ring

theorem exists_unique_fixedPoint (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (η : κ → H2 𝓕 μ T) (u : ν → H2 𝓕 μ T)
    (hc : rate (𝓕:=𝓕) (μ:=μ) T A C < 1) :
    ∃! X, picardMap hW hWm hWc i₀ T A B C D η u X = X := by
  letI : CompleteSpace (κ → H2 𝓕 μ T) := by
    unfold H2
    infer_instance
  have hr := rate_nonneg (𝓕:=𝓕) (μ:=μ) T A C
  have hcontract : ContractingWith (Real.toNNReal (rate (𝓕:=𝓕) (μ:=μ) T A C))
      (picardMap hW hWm hWc i₀ T A B C D η u) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun X Y ↦ ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr, NNReal.coe_one]
      exact hc
    · rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hr]
      exact picardMap_contraction hW hWm hWc i₀ T A B C D η X Y u
  exact ⟨hcontract.fixedPoint _, hcontract.fixedPoint_isFixedPt,
    fun Y hY ↦ hcontract.fixedPoint_unique hY⟩

end LinearStochastic.CommonVectorPicard
