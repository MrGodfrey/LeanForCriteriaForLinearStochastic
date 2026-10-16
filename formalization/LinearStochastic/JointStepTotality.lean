/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

The constant-normalization argument is adapted from MathFin
WienerExponentialTotality; joint coordinate density uses the independently
proved finite-coordinate totality on the original sample space.
-/
import LinearStochastic.JointStepRepresentation
import LinearStochastic.FiniteStepAbel
import LinearStochastic.JointExponentialTotality

noncomputable section
namespace LinearStochastic.JointStepTotality
open MeasureTheory ProbabilityTheory JointDoleansMoments
open scoped NNReal BigOperators
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t))

include hW hWm in
omit [IsProbabilityMeasure μ] in
/-- Orthogonality to actual vector step exponentials implies orthogonality to
all finite coordinate exponentials. The deterministic normalization is positive. -/
theorem integral_mul_exp_linear_eq_zero (T : ℝ≥0) (F : Lp ℝ 2 μ)
    (hperp : ∀ (s : ℕ → ℝ≥0), Monotone s → ∀ (v : ℕ → ι → ℝ) (N : ℕ),
      s 0 = 0 → s N = T → ∫ ω, F ω * stepExp W s v N ω ∂μ = 0)
    {J : Type*} [Fintype J] (t : J → ℝ≥0) (htT : ∀ j, t j ≤ T) (lam : ι → J → ℝ) :
    ∫ ω, F ω * Real.exp (∑ i, ∑ j, lam i j * W i (t j) ω) ∂μ = 0 := by
  obtain ⟨s,N,c,hs,hs0,hsN,hkey⟩ := FiniteStepAbel.exists_step_sum T t htT lam
  have h0 : ∀ᵐ ω ∂μ, ∀ i, W i 0 ω = 0 := by
    rw [ae_all_iff]
    intro i
    exact MathFin.ItoIntegralBrownian.eval_zero_ae (hW i) (hWm i)
  have hk : ∀ᵐ ω ∂μ,
      (∑ k ∈ Finset.range N, ∑ i, c k i * (W i (s (k+1)) ω - W i (s k) ω)) =
        ∑ i, ∑ j, lam i j * W i (t j) ω := by
    filter_upwards [h0] with ω hω
    exact hkey (fun i t => W i t ω) hω
  let C : ℝ := Real.exp (-∑ k ∈ Finset.range N,
    (∑ i, c k i ^ 2) * ((s (k+1) : ℝ) - (s k : ℝ)) / 2)
  have hp (ω : Ω) : stepExp W s c N ω = C * Real.exp
      (∑ k ∈ Finset.range N, ∑ i, c k i * (W i (s (k+1)) ω - W i (s k) ω)) := by
    dsimp [stepExp,C]
    rw [←Real.exp_sum,←Real.exp_add,Finset.sum_sub_distrib]
    congr 1
    ring
  have hh : ∫ ω, C * (F ω * Real.exp
      (∑ k ∈ Finset.range N, ∑ i, c k i * (W i (s (k+1)) ω - W i (s k) ω))) ∂μ = 0 := by
    rw [←hperp s hs c N hs0 hsN]
    apply integral_congr_ae
    filter_upwards with ω
    rw [hp]
    ring
  rw [integral_const_mul] at hh
  have he := (mul_eq_zero.mp hh).resolve_left (Real.exp_pos _).ne'
  rw [integral_congr_ae (g := fun ω => F ω * Real.exp (∑ i, ∑ j, lam i j * W i (t j) ω))
    (by filter_upwards [hk] with ω hω; rw [hω])] at he
  exact he

include hW in
/-- Actual joint-natural L² totality of vector step exponentials, with no
representation hypothesis and no canonical sample-space assumption. -/
theorem eq_zero_of_orthogonal_stepExp
    (hWc : ∀ i ω, Continuous fun t => W i t ω) (T : ℝ≥0) (F : Lp ℝ 2 μ)
    (hFm : AEStronglyMeasurable[JointCylinderGeneration.natural W hWm T] F μ)
    (hperp : ∀ (s : ℕ → ℝ≥0), Monotone s → ∀ (v : ℕ → ι → ℝ) (N : ℕ),
      s 0 = 0 → s N = T → ∫ ω, F ω * stepExp W s v N ω ∂μ = 0) : F = 0 := by
  apply JointExponentialTotality.eq_zero_of_orthogonal_finite_exponentials W hW hWm hWc T F hFm
  intro k lam
  have he := integral_mul_exp_linear_eq_zero W hW hWm T F hperp
    (fun q : {t : ℝ≥0 // t ∈ MathFin.dyadicGrid T k} => (q : ℝ≥0))
    (fun q => MathFin.dyadicGrid_le q.2) (fun i q => lam (i,q))
  simpa only [Fintype.sum_prod_type] using he

end LinearStochastic.JointStepTotality
