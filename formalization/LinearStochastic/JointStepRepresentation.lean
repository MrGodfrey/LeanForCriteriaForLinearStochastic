module

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

The telescoping proof is adapted from MathFin DoleansStepRepresentation to
actual independent Brownian coordinates with their joint natural filtration.
-/
public import LinearStochastic.JointDoleansMoments

@[expose] public section

noncomputable section
namespace LinearStochastic.JointStepRepresentation
open MeasureTheory ProbabilityTheory CommonItoMultichannel JointDoleansMoments JointDoleansBand
open scoped NNReal BigOperators
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t))
  (hInd : iIndepFun (fun i ω t => W i t ω) μ)

omit mΩ in
/-- Algebraic telescoping of the actual vector exponential, without any
probabilistic expectation or representation premise. -/
theorem step_difference (s : ℕ → ℝ≥0) (v : ℕ → ι → ℝ) (n : ℕ) (ω : Ω) :
    (stepExp W s v n ω * Real.exp (-(∑ i, v n i * W i (s n) ω) +
      (∑ i, v n i ^ 2) * (s n : ℝ) / 2)) *
    (exponential W (v n) (s (n+1)) ω - exponential W (v n) (s n) ω) =
      stepExp W s v (n+1) ω - stepExp W s v n ω := by
  have he1 : Real.exp (-(∑ i, v n i * W i (s n) ω) + (∑ i, v n i ^ 2) * (s n : ℝ) / 2) *
      exponential W (v n) (s (n+1)) ω =
      Real.exp ((∑ i, v n i * (W i (s (n+1)) ω - W i (s n) ω)) -
        (∑ i, v n i ^ 2) * ((s (n+1) : ℝ) - (s n : ℝ)) / 2) := by
    unfold exponential
    rw [←Real.exp_add]
    congr 1
    simp_rw [mul_sub,Finset.sum_sub_distrib]
    ring
  have he2 : Real.exp (-(∑ i, v n i * W i (s n) ω) + (∑ i, v n i ^ 2) * (s n : ℝ) / 2) *
      exponential W (v n) (s n) ω = 1 := by
    unfold exponential
    rw [←Real.exp_add]
    rw [show -(∑ i, v n i * W i (s n) ω) + (∑ i, v n i ^ 2) * (s n : ℝ) / 2 +
      ((∑ i, v n i * W i (s n) ω) - (∑ i, v n i ^ 2) * (s n : ℝ) / 2) = 0 by ring,Real.exp_zero]
  rw [mul_assoc,mul_sub,he1,he2]
  simp only [stepExp,Finset.prod_range_succ]
  ring

/-- Every deterministic vector step exponential minus one is an actual sum
of coordinate Ito integrals. The construction retains the exact terminal support. -/
theorem step_mem_range (hWc : ∀ i ω, Continuous fun t => W i t ω)
    (T : ℝ≥0) {s : ℕ → ℝ≥0} (hs : Monotone s) (v : ℕ → ι → ℝ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointCylinderGeneration.natural W hWm) μ :=
      fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
    ∀ n : ℕ, s n ≤ T →
    ∃ φ : ι → Lp ℝ 2 (spacetimeMeasure (JointCylinderGeneration.natural W hWm) μ T),
      (∀ i, ∀ᵐ p ∂spacetimeMeasure (JointCylinderGeneration.natural W hWm) μ T,
        s n < p.1 → φ i p = 0) ∧
      (fun ω => stepExp W s v n ω - 1) =ᵐ[μ]
        sumIntegral (𝓕 := JointCylinderGeneration.natural W hWm) hW hWm T φ := by
  classical
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i)
      (JointCylinderGeneration.natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun _ => 0,fun _ => ?_,?_⟩
    · exact (Lp.coeFn_zero ℝ 2 _).mono (fun p hp _ => hp)
    · have hz : sumIntegral (𝓕 := JointCylinderGeneration.natural W hWm) hW hWm T (fun _ => 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        exact (channelIntegral hW hWm i T).map_zero
      rw [hz]
      filter_upwards [Lp.coeFn_zero ℝ 2 μ] with ω hω
      simpa only [stepExp,Finset.range_zero,Finset.prod_empty,sub_self,Pi.zero_apply] using hω.symm
  | succ n ih =>
    intro hsn1
    have hstep : s n ≤ s (n+1) := hs (Nat.le_succ n)
    obtain ⟨φ,hφsupp,hφval⟩ := ih (hstep.trans hsn1)
    let Z : Ω → ℝ := fun ω => stepExp W s v n ω *
      Real.exp (-(∑ i, v n i * W i (s n) ω) + (∑ i, v n i ^ 2) * (s n : ℝ) / 2)
    have hZm : Measurable[JointCylinderGeneration.natural W hWm (s n)] Z := by
      exact (measurable_stepExp W hWm hs v n).mul
        ((Finset.measurable_sum _ fun i _ =>
          (JointCylinderGeneration.measurable_natural W hWm i le_rfl).const_mul (v n i)).neg.add_const _).exp
    have hZ : MemLp (fun ω => Z ω *
        (exponential W (v n) (s (n+1)) ω - exponential W (v n) (s n) ω)) 2 μ := by
      have he : (fun ω => Z ω *
          (exponential W (v n) (s (n+1)) ω - exponential W (v n) (s n) ω)) =
          fun ω => stepExp W s v (n+1) ω - stepExp W s v n ω :=
        funext (step_difference W s v n)
      rw [he]
      exact (memLp_stepExp W hW hWm s v (n+1)).sub (memLp_stepExp W hW hWm s v n)
    obtain ⟨ψ,_,hψsupp,hψval⟩ := factored_band_mem_range W hW hWm hInd hWc
      (v n) (s n) (s (n+1)) T hstep hsn1 Z hZm hZ
    refine ⟨fun i => φ i + ψ i, ?_, ?_⟩
    · intro i
      filter_upwards [Lp.coeFn_add (φ i) (ψ i),hφsupp i,hψsupp i] with p ha hf hg hp
      rw [ha,Pi.add_apply,hf (lt_of_le_of_lt hstep hp),hg hp,add_zero]
    · have hadd : sumIntegral (𝓕 := JointCylinderGeneration.natural W hWm) hW hWm T
          (fun i => φ i + ψ i) = sumIntegral hW hWm T φ + sumIntegral hW hWm T ψ := by
        unfold sumIntegral
        rw [←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        exact (channelIntegral hW hWm i T).map_add (φ i) (ψ i)
      rw [hadd]
      filter_upwards [Lp.coeFn_add (sumIntegral hW hWm T φ) (sumIntegral hW hWm T ψ),
        hφval,hψval] with ω ha hf hg
      rw [ha,Pi.add_apply,←hf,←hg]
      change stepExp W s v (n+1) ω - 1 = stepExp W s v n ω - 1 + Z ω * _
      rw [show Z ω * (exponential W (v n) (s (n+1)) ω - exponential W (v n) (s n) ω) =
        stepExp W s v (n+1) ω - stepExp W s v n ω from step_difference W s v n ω]
      ring

end LinearStochastic.JointStepRepresentation
