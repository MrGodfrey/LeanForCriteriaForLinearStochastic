module

public import LinearStochastic.LpLyapunovEstimate

@[expose] public section

/-! Passing from expected quadratic energy to the actual second moment,
with the precise ratio of lower and upper pointwise constants. -/
noncomputable section
namespace LinearStochastic.QuadraticMomentBounds
open MeasureTheory
open scoped InnerProductSpace
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem integrated_bounds (H : E →L[ℝ] E) (a b : ℝ)
    (hl : ∀ x, a*‖x‖^2 ≤ inner ℝ x (H x))
    (hu : ∀ x, inner ℝ x (H x) ≤ b*‖x‖^2)
    (X : Ω → E) (hX : MemLp X 2 μ) :
    a * (∫ ω, ‖X ω‖^2 ∂μ) ≤ (∫ ω, inner ℝ (X ω) (H (X ω)) ∂μ) ∧
      (∫ ω, inner ℝ (X ω) (H (X ω)) ∂μ) ≤ b * (∫ ω, ‖X ω‖^2 ∂μ) := by
  have he := DriftMartingaleDuality.integrable_inner_of_memLp hX (H.comp_memLp' hX)
  have hn : Integrable (fun ω => ‖X ω‖^2) μ := hX.norm.integrable_sq
  have hlo := integral_mono (hn.const_mul a) he (fun ω => hl (X ω))
  have hhi := integral_mono he (hn.const_mul b) (fun ω => hu (X ω))
  rw [integral_const_mul] at hlo hhi
  exact ⟨hlo,hhi⟩

theorem moment_le_of_energy_le (H : E →L[ℝ] E) (a b d : ℝ) (ha : 0 < a) (hd : 0 ≤ d)
    (hl : ∀ x, a*‖x‖^2 ≤ inner ℝ x (H x))
    (hu : ∀ x, inner ℝ x (H x) ≤ b*‖x‖^2)
    (X ξ : Ω → E) (hX : MemLp X 2 μ) (hξ : MemLp ξ 2 μ)
    (he : (∫ ω, inner ℝ (X ω) (H (X ω)) ∂μ) ≤ d * ∫ ω, inner ℝ (ξ ω) (H (ξ ω)) ∂μ) :
    (∫ ω, ‖X ω‖^2 ∂μ) ≤ (b/a)*d*(∫ ω, ‖ξ ω‖^2 ∂μ) := by
  have hlo := (integrated_bounds H a b hl hu X hX).1
  have hhi := (integrated_bounds H a b hl hu ξ hξ).2
  rw [show (b/a)*d*(∫ ω, ‖ξ ω‖^2 ∂μ) = (d*(b*(∫ ω, ‖ξ ω‖^2 ∂μ)))/a from by ring]
  apply (le_div_iff₀ ha).mpr
  calc
    (∫ ω, ‖X ω‖^2 ∂μ)*a ≤ ∫ ω, inner ℝ (X ω) (H (X ω)) ∂μ := by simpa only [mul_comm] using hlo
    _ ≤ d*(∫ ω, inner ℝ (ξ ω) (H (ξ ω)) ∂μ) := he
    _ ≤ d*(b*(∫ ω, ‖ξ ω‖^2 ∂μ)) := mul_le_mul_of_nonneg_left hhi hd

end LinearStochastic.QuadraticMomentBounds
