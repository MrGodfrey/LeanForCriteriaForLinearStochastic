module

public import LinearStochastic.LMIPolynomial
public import Mathlib.Analysis.Matrix.Spectrum

@[expose] public section

noncomputable section
namespace LinearStochastic.MatrixGrowthBounds
open scoped BigOperators Matrix.Norms.Frobenius InnerProductSpace
open LMIPolynomial MatrixNormalization
variable {n r m : ℕ}

theorem operator_apply_bound (P : Matrix (Fin r) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ‖P.toEuclideanLin x‖ ≤ ‖P‖*‖x‖ := by
  have hs : ‖P.toEuclideanLin x‖^2 ≤ (‖P‖*‖x‖)^2 := by
    simp only [mul_pow,PiLp.norm_sq_eq_of_L2,frobenius_sq,Matrix.toLpLin_apply,
      Real.norm_eq_abs,sq_abs,Matrix.mulVec,dotProduct]
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  nlinarith [norm_nonneg (P.toEuclideanLin x),norm_nonneg P,norm_nonneg x,
    mul_nonneg (norm_nonneg P) (norm_nonneg x)]

/-- The Euclidean operator norm is bounded by the actual Frobenius norm. -/
theorem operator_norm_le_frobenius (P : Matrix (Fin r) (Fin n) ℝ) :
    ‖P.toEuclideanLin.toContinuousLinearMap‖ ≤ ‖P‖ := by
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg P) (operator_apply_bound P)

theorem eigenvector_action (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsHermitian) (i : Fin n) :
    P.toEuclideanLin (hP.eigenvectorBasis i) = hP.eigenvalues i • hP.eigenvectorBasis i := by
  apply WithLp.ofLp_injective
  exact hP.mulVec_eigenvectorBasis i

theorem eigenvalue_le_frobenius (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.IsHermitian) (i : Fin n) : hP.eigenvalues i ≤ ‖P‖ := by
  have h := operator_apply_bound P (hP.eigenvectorBasis i)
  rw [eigenvector_action, norm_smul,hP.eigenvectorBasis.norm_eq_one, mul_one,mul_one] at h
  exact (le_abs_self _).trans h

/-- P ≥ I bounds every genuine eigenvalue from below by one. -/
theorem eigenvalue_ge_one (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsHermitian)
    (h : (P-1).PosSemidef) (i : Fin n) : 1 ≤ hP.eigenvalues i := by
  have hi := (Matrix.isPositive_toEuclideanLin_iff.mpr h).2 (hP.eigenvectorBasis i)
  change 0 ≤ inner ℝ ((P-1).toEuclideanLin (hP.eigenvectorBasis i)) (hP.eigenvectorBasis i) at hi
  rw [map_sub,Matrix.toLpLin_one,LinearMap.sub_apply,LinearMap.id_apply,
    eigenvector_action,inner_sub_left,inner_smul_left,conj_trivial,
    real_inner_self_eq_norm_sq,hP.eigenvectorBasis.norm_eq_one] at hi
  norm_num at hi ⊢
  linarith

/-- The actual largest and smallest eigenvalues, with multiplicity harmless. -/
def maxEigenvalue [Nonempty (Fin n)] (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hP.eigenvalues

def minEigenvalue [Nonempty (Fin n)] (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsHermitian) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hP.eigenvalues

/-- The manuscript's spectral condition number λmax(P)/λmin(P). -/
def conditionNumber [Nonempty (Fin n)] (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsHermitian) : ℝ :=
  maxEigenvalue P hP / minEigenvalue P hP

theorem conditionNumber_le_frobenius [Nonempty (Fin n)]
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.IsHermitian) (h : (P-1).PosSemidef) :
    conditionNumber P hP ≤ ‖P‖ := by
  have hlo : 1 ≤ minEigenvalue P hP := Finset.le_inf' _ _ (fun i _ => eigenvalue_ge_one P hP h i)
  have hhi : maxEigenvalue P hP ≤ ‖P‖ := Finset.sup'_le _ _ (fun i _ => eigenvalue_le_frobenius P hP i)
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hlo)).mpr
  exact hhi.trans (le_mul_of_one_le_right (norm_nonneg P) hlo)

theorem objective_ge_one [Nonempty (Fin n)] (P : Matrix (Fin n) (Fin n) ℝ)
    (K : Matrix (Fin r) (Fin n) ℝ) (hP : P.IsHermitian) (h : (P-1).PosSemidef) :
    1 ≤ QuadraticMinimum.matrixObjective (P,K) := by
  let i : Fin n := Classical.arbitrary _
  have hl := eigenvalue_ge_one P hP h i
  have hu := eigenvalue_le_frobenius P hP i
  dsimp [QuadraticMinimum.matrixObjective,QuadraticMinimum.objective]
  nlinarith [sq_nonneg ‖K‖]

theorem conditionNumber_le_objective [Nonempty (Fin n)]
    (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (hP : P.IsHermitian) (h : (P-1).PosSemidef) :
    conditionNumber P hP ≤ QuadraticMinimum.matrixObjective (P,K) := by
  have hc := conditionNumber_le_frobenius P hP h
  let i : Fin n := Classical.arbitrary _
  have hl := (eigenvalue_ge_one P hP h i).trans (eigenvalue_le_frobenius P hP i)
  dsimp [QuadraticMinimum.matrixObjective,QuadraticMinimum.objective]
  nlinarith [sq_nonneg ‖K‖]

/-- The exact gain K P⁻¹, measured in Euclidean operator norm, is controlled
by the Frobenius objective of every normalized feasible pair. -/
theorem feasible_gain_bound
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (h : Feasible A B C D ρ P K) (i : Fin m) :
    ‖(K*P⁻¹).toEuclideanLin.toContinuousLinearMap‖^2 ≤ QuadraticMinimum.matrixObjective (P,K) := by
  have hb : ‖(K*P⁻¹).toEuclideanLin.toContinuousLinearMap‖ ≤ ‖K‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg K)
    intro x
    change ‖(K*P⁻¹).toEuclideanLin x‖ ≤ ‖K‖*‖x‖
    rw [Matrix.toLpLin_mul_same,LinearMap.comp_apply]
    exact (operator_apply_bound K _).trans
      (mul_le_mul_of_nonneg_left (feasible_inverse_bound A B C D ρ P K h i x) (norm_nonneg K))
  dsimp [QuadraticMinimum.matrixObjective,QuadraticMinimum.objective]
  nlinarith [norm_nonneg (K*P⁻¹).toEuclideanLin.toContinuousLinearMap,norm_nonneg K,sq_nonneg ‖P‖]

end LinearStochastic.MatrixGrowthBounds
