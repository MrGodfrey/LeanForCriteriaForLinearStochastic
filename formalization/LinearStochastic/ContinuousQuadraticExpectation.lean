module

public import LinearStochastic.ContinuousDoobL2
public import LinearStochastic.LinearDuality

@[expose] public section

/-! Continuous S² paths have continuous actual expected quadratic products.
The dominating integrable function is the genuine squared path supremum. -/
noncomputable section
namespace LinearStochastic.ContinuousQuadraticExpectation
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace
open ContinuousDoobL2
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem continuousOn_expected_product (T : ℝ≥0) (R : ℝ≥0 → Ω → E)
    (hm : ∀ t, AEStronglyMeasurable (R t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (h2 : MemLp (pathSup R T) 2 μ) (A B : E →L[ℝ] E) :
    ContinuousOn (fun t => ∫ ω, inner ℝ (A (R t ω)) (B (R t ω)) ∂μ) (Iic T) := by
  apply continuousOn_of_dominated (bound := fun ω => (‖A‖ * ‖B‖) * (pathSup R T ω)^2)
  · intro t _
    exact (A.continuous.comp_aestronglyMeasurable (hm t)).inner
      (B.continuous.comp_aestronglyMeasurable (hm t))
  · intro t ht
    filter_upwards [hc] with ω hc
    have hcomp : IsCompact (Iic T) := by rw [← Icc_bot]; exact isCompact_Icc
    have hb : BddAbove (range (fun s : Iic T => ‖R s.val ω‖)) := by
      simpa only [image_eq_range] using hcomp.bddAbove_image hc.norm
    have hs : ‖R t ω‖ ≤ pathSup R T ω := le_ciSup hb ⟨t,ht⟩
    calc
      ‖inner ℝ (A (R t ω)) (B (R t ω))‖ ≤ ‖A (R t ω)‖ * ‖B (R t ω)‖ := norm_inner_le_norm _ _
      _ ≤ (‖A‖ * ‖R t ω‖) * (‖B‖ * ‖R t ω‖) :=
        mul_le_mul (A.le_opNorm _) (B.le_opNorm _) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = (‖A‖ * ‖B‖) * ‖R t ω‖^2 := by ring
      _ ≤ (‖A‖ * ‖B‖) * (pathSup R T ω)^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hs 2)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · exact h2.integrable_sq.const_mul _
  · filter_upwards [hc] with ω hc
    exact (A.continuous.comp_continuousOn hc).inner (B.continuous.comp_continuousOn hc)

end LinearStochastic.ContinuousQuadraticExpectation
