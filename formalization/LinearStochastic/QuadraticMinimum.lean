import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

noncomputable section
namespace LinearStochastic.QuadraticMinimum
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

def objective (z : E × F) : ℝ := ‖z.1‖^2 + ‖z.2‖^2

theorem objective_continuous : Continuous (objective : E × F → ℝ) :=
  (continuous_fst.norm.pow 2).add (continuous_snd.norm.pow 2)

theorem objective_nonneg (z : E × F) : 0 ≤ objective z := add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem norm_le_objective_add_one (z : E × F) : ‖z‖ ≤ objective z + 1 := by
  rw [Prod.norm_def, max_le_iff]
  constructor <;> dsimp [objective] <;> nlinarith [sq_nonneg (‖z.1‖-1),sq_nonneg (‖z.2‖-1),
    sq_nonneg ‖z.1‖,sq_nonneg ‖z.2‖]

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Coercivity and compactness are proved here, not included as premises. -/
theorem exists_minimum (S : Set (E × F)) (hclosed : IsClosed S) (hne : S.Nonempty) :
    ∃ z ∈ S, ∀ w ∈ S, objective z ≤ objective w := by
  obtain ⟨z₀,h₀⟩ := hne
  let R : ℝ := objective z₀ + 1
  let K := S ∩ Metric.closedBall (0 : E × F) R
  have hK : IsCompact K := (isCompact_closedBall (0 : E × F) R).inter_left hclosed
  have hz₀ : z₀ ∈ K := ⟨h₀, by simpa only [Metric.mem_closedBall, dist_zero_right]
    using norm_le_objective_add_one z₀⟩
  obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn ⟨z₀,hz₀⟩ objective_continuous.continuousOn
  refine ⟨z,hz.1,fun w hw => ?_⟩
  by_cases hb : ‖w‖ ≤ R
  · exact hmin ⟨hw,by simpa only [Metric.mem_closedBall,dist_zero_right] using hb⟩
  · have hzle : objective z ≤ objective z₀ := hmin hz₀
    have hwb := norm_le_objective_add_one w
    dsimp only [R] at hb
    linarith

open scoped Matrix.Norms.Frobenius
variable {n r : ℕ}

/-- The objective is literally the sum of squared Frobenius matrix norms. -/
def matrixObjective (z : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin r) (Fin n) ℝ) : ℝ :=
  objective z

theorem matrixObjective_continuous : Continuous (matrixObjective (n := n) (r := r)) :=
  objective_continuous

theorem matrix_minimum (S : Set (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin r) (Fin n) ℝ))
    (hclosed : IsClosed S) (hne : S.Nonempty) :
    ∃ z ∈ S, ∀ w ∈ S, matrixObjective z ≤ matrixObjective w :=
  exists_minimum S hclosed hne

#print axioms matrix_minimum
end LinearStochastic.QuadraticMinimum
