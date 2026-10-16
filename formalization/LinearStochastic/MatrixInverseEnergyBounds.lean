import LinearStochastic.MatrixFeedback
import LinearStochastic.MatrixGrowthBounds
import Mathlib.Analysis.Matrix.PosDef

/-! Exact spectral bounds for the ordinary inverse P⁻¹.  The constants are
the manuscript's actual smallest and largest eigenvalues of P. -/
noncomputable section
namespace LinearStochastic.MatrixInverseEnergyBounds
open scoped BigOperators InnerProductSpace
open MatrixGrowthBounds
variable {n : ℕ} [Nonempty (Fin n)]

theorem min_eigen_pos (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) :
    0 < minEigenvalue P hP.isHermitian := by
  exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hP.eigenvalues_pos i)

theorem max_eigen_pos (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) :
    0 < maxEigenvalue P hP.isHermitian := by
  let i : Fin n := Classical.arbitrary _
  exact (hP.eigenvalues_pos i).trans_le (Finset.le_sup' _ (Finset.mem_univ i))

omit [Nonempty (Fin n)] in
theorem inverse_eigenvector (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) (i : Fin n) :
    P⁻¹.toEuclideanLin (hP.isHermitian.eigenvectorBasis i) =
      (hP.isHermitian.eigenvalues i)⁻¹ • hP.isHermitian.eigenvectorBasis i := by
  rw [← MatrixFeedback.inverse_matrix P hP]
  apply LMIFeedback.positive_injective P.toEuclideanLin (PositiveFinite.matrix_uniformPositive P hP)
  rw [LMIFeedback.apply_inverse,map_smul,eigenvector_action,smul_smul,
    inv_mul_cancel₀ (ne_of_gt (hP.eigenvalues_pos i)),one_smul]

omit [Nonempty (Fin n)] in
theorem inverse_quadratic_expansion (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x (P⁻¹.toEuclideanLin x) =
      ∑ i, (hP.isHermitian.eigenvalues i)⁻¹ * (inner ℝ (hP.isHermitian.eigenvectorBasis i) x)^2 := by
  have hs : P⁻¹.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hP.inv.isHermitian
  rw [← hP.isHermitian.eigenvectorBasis.sum_inner_mul_inner x (P⁻¹.toEuclideanLin x)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hs, inverse_eigenvector P hP,inner_smul_left,conj_trivial,real_inner_comm x]
  ring

theorem inverse_quadratic_bounds (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    (x : EuclideanSpace ℝ (Fin n)) :
    (maxEigenvalue P hP.isHermitian)⁻¹ * ‖x‖^2 ≤ inner ℝ x (P⁻¹.toEuclideanLin x) ∧
      inner ℝ x (P⁻¹.toEuclideanLin x) ≤ (minEigenvalue P hP.isHermitian)⁻¹ * ‖x‖^2 := by
  rw [inverse_quadratic_expansion P hP,← hP.isHermitian.eigenvectorBasis.sum_sq_inner_right x]
  simp only [Finset.mul_sum]
  constructor
  · apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact inv_anti₀ (hP.eigenvalues_pos i) (Finset.le_sup' _ (Finset.mem_univ i))
  · apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact inv_anti₀ (min_eigen_pos P hP) (Finset.inf'_le _ (Finset.mem_univ i))

end LinearStochastic.MatrixInverseEnergyBounds
