import MathFin.Foundations.SDEExistence

/-!
# Local scalar SDEs from a constructed Itô integral

Uses formal-mathfin at 99b836298731c432a6242fdb6cb51c1c97f37902.
The integrals and Picard map are constructed by the dependency; neither is
postulated in this file. This gives existence and uniqueness in predictable
spacetime L² for a short time interval and the scalar Brownian natural filtration.
It does not assert the paper's vector, joint-filtration, global-time S² theorem.
-/

namespace LinearStochastic.MathFinBridge

open MeasureTheory ProbabilityTheory
open scoped NNReal
open MathFin.SDEExistence MathFin.ItoIntegralCLM
open MathFin.ItoIntegralProcessContinuousModification

/-- The Brownian assumptions are realized by a constructed Gaussian model. -/
theorem canonical_brownian_foundation :
    IsPreBrownianReal brownian gaussianLimit ∧
      (∀ t, Measurable (brownian t)) ∧
      (∀ ω, Continuous (fun t : ℝ≥0 ↦ brownian t ω)) :=
  ⟨isBrownianReal_brownian.toIsPreBrownianReal, measurable_brownian, continuous_brownian⟩

theorem affine_lipschitz (a b : ℝ) :
    LipschitzWith ‖a‖₊ (fun x : ℝ ↦ a * x + b) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  simp only [Real.dist_eq, add_sub_add_right_eq_sub, ← mul_sub, abs_mul,
    coe_nnnorm, Real.norm_eq_abs, le_refl]

theorem linear_lipschitz (a : ℝ) :
    LipschitzWith ‖a‖₊ (fun x : ℝ ↦ a * x) := by
  simpa using affine_lipschitz a 0

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}

/-- The integrals are the library's constructed operators, not assumptions. -/
theorem affine_sde_local_exists_unique
    (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ B t ω))
    (a b c d x₀ : ℝ)
    (hsmall : (T : ℝ) * ‖a‖ + Real.sqrt (T : ℝ) * ‖c‖ < 1) :
    ∃! X : Lp ℝ 2 (trimMeasure_T (μ := P) T hBmeas),
      Lp.const 2 (trimMeasure_T (μ := P) T hBmeas) x₀
        + driftProcessAssembled T hBmeas
            (lipComp T hBmeas (fun x ↦ a * x + b) ‖a‖₊ (affine_lipschitz a b) X)
        + itoProcessAssembled hB T hBmeas hBcont
            (lipComp T hBmeas (fun x ↦ c * x + d) ‖c‖₊ (affine_lipschitz c d) X) = X := by
  exact picardMap_exists_unique_fixedPoint hB T hBmeas hBcont
    (affine_lipschitz a b) (affine_lipschitz c d)
    (Lp.const 2 (trimMeasure_T (μ := P) T hBmeas) x₀) hsmall

/-- A genuine predictable L² control enters both drift and diffusion. -/
theorem controlled_scalar_sde_local_exists_unique
    (hB : IsPreBrownianReal B P) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t))
    (hBcont : ∀ ω, Continuous (fun t : ℝ≥0 ↦ B t ω))
    (a b c d x₀ : ℝ) (u : Lp ℝ 2 (trimMeasure_T (μ := P) T hBmeas))
    (hsmall : (T : ℝ) * ‖a‖ + Real.sqrt (T : ℝ) * ‖c‖ < 1) :
    ∃! X : Lp ℝ 2 (trimMeasure_T (μ := P) T hBmeas),
      Lp.const 2 (trimMeasure_T (μ := P) T hBmeas) x₀
        + driftProcessAssembled T hBmeas
            (lipComp T hBmeas (fun x ↦ a * x) ‖a‖₊ (linear_lipschitz a) X + b • u)
        + itoProcessAssembled hB T hBmeas hBcont
            (lipComp T hBmeas (fun x ↦ c * x) ‖c‖₊ (linear_lipschitz c) X + d • u) = X := by
  let initial : Lp ℝ 2 (trimMeasure_T (μ := P) T hBmeas) :=
    Lp.const 2 (trimMeasure_T (μ := P) T hBmeas) x₀
      + driftProcessAssembled T hBmeas (b • u)
      + itoProcessAssembled hB T hBmeas hBcont (d • u)
  have rewrite_map (X : Lp ℝ 2 (trimMeasure_T (μ := P) T hBmeas)) :
      Lp.const 2 (trimMeasure_T (μ := P) T hBmeas) x₀
        + driftProcessAssembled T hBmeas
            (lipComp T hBmeas (fun x ↦ a * x) ‖a‖₊ (linear_lipschitz a) X + b • u)
        + itoProcessAssembled hB T hBmeas hBcont
            (lipComp T hBmeas (fun x ↦ c * x) ‖c‖₊ (linear_lipschitz c) X + d • u) =
      picardMap hB T hBmeas hBcont (linear_lipschitz a) (linear_lipschitz c) initial X := by
    rw [map_add, itoProcessAssembled_add]
    dsimp [picardMap, initial]
    abel
  obtain ⟨X, hX, unique⟩ := picardMap_exists_unique_fixedPoint hB T hBmeas hBcont
    (linear_lipschitz a) (linear_lipschitz c) initial hsmall
  refine ⟨X, (rewrite_map X).trans hX, ?_⟩
  intro Y hY
  exact unique Y ((rewrite_map Y).symm.trans hY)

end LinearStochastic.MathFinBridge
