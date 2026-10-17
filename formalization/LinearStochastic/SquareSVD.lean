module

public import LinearStochastic.SpectralNullspace

@[expose] public section

/-! A genuine paired square SVD, constructed from the spectral theorem and orthonormal extension. -/
noncomputable section
namespace LinearStochastic.SquareSVD
open Module
open scoped BigOperators InnerProductSpace
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
open SpectralNullspace

def normalizedImage (T : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E)) : F :=
  (T.singularValues i)⁻¹ • T (rightBasis T i)

theorem image_inner (T : E →ₗ[ℝ] F) (i j : Fin (finrank ℝ E)) :
    ⟪T (rightBasis T i), T (rightBasis T j)⟫_ℝ =
      T.singularValues j ^ 2 * (if i = j then 1 else 0) := by
  rw [← T.adjoint_inner_right]
  have he := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl j
  change T.adjoint (T (rightBasis T j)) =
    (T.isSymmetric_adjoint_comp_self.eigenvalues rfl j) • rightBasis T j at he
  rw [he, inner_smul_right]
  rw [← T.sq_singularValues_fin rfl j, OrthonormalBasis.inner_eq_ite]

theorem normalized_orthonormal (T : E →ₗ[ℝ] F) :
    Orthonormal ℝ (({i : Fin (finrank ℝ E) | T.singularValues i ≠ 0}).domRestrict
      (normalizedImage T)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  change ⟪(T.singularValues i.val)⁻¹ • T (rightBasis T i.val),
    (T.singularValues j.val)⁻¹ • T (rightBasis T j.val)⟫_ℝ = _
  rw [inner_smul_left, inner_smul_right, image_inner]
  simp only [conj_trivial]
  by_cases hij : i = j
  · subst j
    simp only [ite_true]
    have hn : T.singularValues i.val ≠ 0 := i.property
    field_simp
  · have hval : i.val ≠ j.val := fun he => hij (Subtype.ext he)
    simp [hij, hval]

/-- The left singular basis is actually extended from normalized images of positive right vectors. -/
def leftBasis (T : E →ₗ[ℝ] F) (hd : finrank ℝ F = finrank ℝ E) :
    OrthonormalBasis (Fin (finrank ℝ E)) ℝ F :=
  ((normalized_orthonormal T).exists_orthonormalBasis_extension_of_card_eq
    (by simpa only [Fintype.card_fin] using hd)).choose

theorem leftBasis_positive (T : E →ₗ[ℝ] F) (hd : finrank ℝ F = finrank ℝ E)
    (i : Fin (finrank ℝ E)) (hi : T.singularValues i ≠ 0) :
    leftBasis T hd i = normalizedImage T i :=
  ((normalized_orthonormal T).exists_orthonormalBasis_extension_of_card_eq
    (by simpa only [Fintype.card_fin] using hd)).choose_spec i hi

theorem singular_pair (T : E →ₗ[ℝ] F) (hd : finrank ℝ F = finrank ℝ E)
    (i : Fin (finrank ℝ E)) :
    T (rightBasis T i) = T.singularValues i • leftBasis T hd i := by
  by_cases hi : T.singularValues i = 0
  · rw [hi, zero_smul]
    change rightBasis T i ∈ T.ker
    rw [ker_eq_zero_singular_span]
    exact Submodule.subset_span ⟨i, T.singularValues_eq_zero_iff_le_finrank_range.mp hi, rfl⟩
  · rw [leftBasis_positive T hd i hi, normalizedImage, smul_smul, mul_inv_cancel₀ hi, one_smul]

/-- This is the full UΣVᵀ equality, not a factorization assumption. -/
theorem decomposition (T : E →ₗ[ℝ] F) (hd : finrank ℝ F = finrank ℝ E) (x : E) :
    T x = ∑ i, ((rightBasis T).repr x i * T.singularValues i) • leftBasis T hd i := by
  conv_lhs => rw [← (rightBasis T).sum_repr x]
  simp only [map_sum, map_smul, singular_pair T hd, smul_smul]

theorem adjoint_coordinates (T : E →ₗ[ℝ] F) (hd : finrank ℝ F = finrank ℝ E)
    (x : F) (i : Fin (finrank ℝ E)) :
    (rightBasis T).repr (T.adjoint x) i =
      T.singularValues i * (leftBasis T hd).repr x i := by
  rw [OrthonormalBasis.repr_apply_apply, T.adjoint_inner_right, singular_pair T hd,
    inner_smul_left, OrthonormalBasis.repr_apply_apply, conj_trivial]

theorem left_ker_iff_coordinates (T : E →ₗ[ℝ] F) (hd : finrank ℝ F = finrank ℝ E) (x : F) :
    x ∈ T.adjoint.ker ↔ ∀ i : Fin (finrank ℝ E), i.val < finrank ℝ T.range →
      (leftBasis T hd).repr x i = 0 := by
  constructor
  · intro hx i hi
    have h := adjoint_coordinates T hd x i
    rw [show T.adjoint x = 0 from hx, map_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left
      (ne_of_gt (T.singularValues_pos_iff_lt_finrank_range.mpr hi))
  · intro hx
    apply (rightBasis T).repr.injective
    ext i
    rw [map_zero]
    change (rightBasis T).repr (T.adjoint x) i = 0
    rw [adjoint_coordinates T hd]
    by_cases hi : i.val < finrank ℝ T.range
    · rw [hx i hi, mul_zero]
    · rw [T.singularValues_eq_zero_iff_le_finrank_range.mpr (Nat.le_of_not_gt hi), zero_mul]

theorem left_ker_eq_zero_span (T : E →ₗ[ℝ] F) (hd : finrank ℝ F = finrank ℝ E) :
    T.adjoint.ker = Submodule.span ℝ ((leftBasis T hd) ''
      {i : Fin (finrank ℝ E) | finrank ℝ T.range ≤ i.val}) := by
  ext x
  rw [left_ker_iff_coordinates T hd]
  rw [← OrthonormalBasis.coe_toBasis, Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq,
    OrthonormalBasis.coe_toBasis_repr_apply]
  constructor
  · intro h i hi
    by_contra hn
    exact hi (h i (Nat.lt_of_not_ge hn))
  · intro h i hi
    by_contra hn
    exact Nat.not_le_of_gt hi (h i hn)
end LinearStochastic.SquareSVD
