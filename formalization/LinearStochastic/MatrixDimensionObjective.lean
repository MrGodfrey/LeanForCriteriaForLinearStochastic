import LinearStochastic.MatrixGrowthBounds

noncomputable section
namespace LinearStochastic.MatrixDimensionObjective
open scoped BigOperators Matrix.Norms.Frobenius
open LMIPolynomial MatrixNormalization
variable {n r m : ℕ}

/-- The dimension lower bound in the manuscript: P ≥ I forces the squared
Frobenius norm to dominate the number of state coordinates, including n = 0. -/
theorem dimension_le_frobenius_sq (P : Matrix (Fin n) (Fin n) ℝ)
    (h : (P - 1).PosSemidef) : (n : ℝ) ≤ ‖P‖ ^ 2 := by
  have hd (i : Fin n) : 1 ≤ P i i := by
    have hi := h.diag_nonneg (i := i)
    simpa only [Matrix.sub_apply,Matrix.one_apply_eq,sub_nonneg] using hi
  calc
    (n : ℝ) = ∑ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ ∑ i : Fin n, P i i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [hd i]
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, P i j ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.single_le_sum (fun j _ => sq_nonneg (P i j)) (Finset.mem_univ i)
    _ = ‖P‖ ^ 2 := (frobenius_sq P).symm

/-- The exact Frobenius minimization objective is at least n on every
normalized feasible pair, without requiring n > 0 as a hidden instance. -/
theorem dimension_le_objective (P : Matrix (Fin n) (Fin n) ℝ)
    (K : Matrix (Fin r) (Fin n) ℝ) (h : (P - 1).PosSemidef) :
    (n : ℝ) ≤ QuadraticMinimum.matrixObjective (P,K) := by
  have hp := dimension_le_frobenius_sq P h
  dsimp [QuadraticMinimum.matrixObjective,QuadraticMinimum.objective]
  nlinarith [sq_nonneg ‖K‖]

theorem feasible_dimension_le_objective
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (h : Feasible A B C D ρ P K) (i : Fin m) :
    (n : ℝ) ≤ QuadraticMinimum.matrixObjective (P,K) :=
  dimension_le_objective P K (feasible_ge_one A B C D ρ P K h i)

#print axioms dimension_le_frobenius_sq
#print axioms feasible_dimension_le_objective
end LinearStochastic.MatrixDimensionObjective
