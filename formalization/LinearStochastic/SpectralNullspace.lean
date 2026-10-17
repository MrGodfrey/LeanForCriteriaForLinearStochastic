module

public import LinearStochastic.AlgebraStaircase
public import Mathlib.Analysis.InnerProductSpace.SingularValues

@[expose] public section

/-! Actual full right/left singular bases and their zero singular subspaces. -/
noncomputable section
namespace LinearStochastic.SpectralNullspace
open Module
open scoped BigOperators InnerProductSpace
variable {E F X : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

def rightBasis (T : E →ₗ[ℝ] F) : OrthonormalBasis (Fin (finrank ℝ E)) ℝ E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

def leftBasis (T : E →ₗ[ℝ] F) : OrthonormalBasis (Fin (finrank ℝ F)) ℝ F :=
  rightBasis T.adjoint

theorem right_diagonal (T : E →ₗ[ℝ] F) (x : E) (i : Fin (finrank ℝ E)) :
    (rightBasis T).repr (T.adjoint (T x)) i =
      (T.singularValues i)^2 * (rightBasis T).repr x i := by
  rw [T.sq_singularValues_fin rfl]
  exact T.isSymmetric_adjoint_comp_self.eigenvectorBasis_apply_self_apply rfl x i

theorem ker_iff_coordinates (T : E →ₗ[ℝ] F) (x : E) :
    x ∈ T.ker ↔ ∀ i : Fin (finrank ℝ E), i.val < finrank ℝ T.range →
      (rightBasis T).repr x i = 0 := by
  rw [← T.ker_adjoint_comp_self]
  constructor
  · intro hx i hi
    have h := right_diagonal T x i
    have hz : (T.adjoint ∘ₗ T) x = 0 := hx
    change T.adjoint (T x) = 0 at hz
    rw [hz, map_zero] at h
    have hp := (T.singularValues_pos_iff_lt_finrank_range).mpr hi
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (ne_of_gt hp))
  · intro hx
    apply (rightBasis T).repr.injective
    ext i
    rw [map_zero]
    change (rightBasis T).repr (T.adjoint (T x)) i = 0
    rw [right_diagonal]
    by_cases hi : i.val < finrank ℝ T.range
    · rw [hx i hi, mul_zero]
    · rw [(T.singularValues_eq_zero_iff_le_finrank_range).mpr (Nat.le_of_not_gt hi)]
      simp

theorem ker_eq_zero_singular_span (T : E →ₗ[ℝ] F) :
    T.ker = Submodule.span ℝ ((rightBasis T) ''
      {i : Fin (finrank ℝ E) | finrank ℝ T.range ≤ i.val}) := by
  ext x
  rw [ker_iff_coordinates]
  rw [← OrthonormalBasis.coe_toBasis, Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq,
    OrthonormalBasis.coe_toBasis_repr_apply]
  constructor
  · intro h i hi
    by_contra hn
    exact hi (h i (Nat.lt_of_not_ge hn))
  · intro h i hi
    by_contra hn
    exact (Nat.not_le_of_gt hi) (h i hn)

theorem left_ker_eq_zero_singular_span (T : E →ₗ[ℝ] F) :
    T.adjoint.ker = Submodule.span ℝ ((leftBasis T) ''
      {i : Fin (finrank ℝ F) | finrank ℝ T.range ≤ i.val}) := by
  simpa only [leftBasis, LinearMap.finrank_range_adjoint] using ker_eq_zero_singular_span T.adjoint

/-- A concrete orthonormal frame of the full spectral zero space, with no factorization premise. -/
def rightZeroFrame (T : E →ₗ[ℝ] F) :=
  Staircase.frame (Submodule.span ℝ ((rightBasis T) ''
    {i : Fin (finrank ℝ E) | finrank ℝ T.range ≤ i.val}))

theorem rightZeroFrame_range (T : E →ₗ[ℝ] F) :
    (rightZeroFrame T).range = T.ker := by
  rw [rightZeroFrame, Staircase.frame_range, ← ker_eq_zero_singular_span]

def leftZeroFrame (T : E →ₗ[ℝ] F) := rightZeroFrame T.adjoint

theorem leftZeroFrame_range (T : E →ₗ[ℝ] F) :
    (leftZeroFrame T).range = T.adjoint.ker := rightZeroFrame_range T.adjoint

theorem spectral_residual_exact (L : X →ₗ[ℝ] F) (M : E →ₗ[ℝ] F) :
    feasibleSpace L M = ((leftZeroFrame M).toLinearMap.adjoint.comp L).ker :=
  ReducedElimination.feasible_eq_residual_ker L M _ (leftZeroFrame_range M)

/-- A full right factor retains every kernel direction, including a wide matrix's omitted tail. -/
theorem wide_tail_in_kernel (T : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E))
    (hi : finrank ℝ F ≤ i.val) : T ((rightBasis T) i) = 0 := by
  change (rightBasis T) i ∈ T.ker
  rw [ker_eq_zero_singular_span]
  apply Submodule.subset_span
  exact ⟨i, le_trans (Submodule.finrank_le T.range) hi, rfl⟩

theorem wide_tail_not_in_thin_span (T : E →ₗ[ℝ] F) (i : Fin (finrank ℝ E))
    (hi : finrank ℝ F ≤ i.val) :
    (rightBasis T) i ∉ Submodule.span ℝ ((rightBasis T) ''
      {j : Fin (finrank ℝ E) | j.val < finrank ℝ F}) := by
  rw [← OrthonormalBasis.coe_toBasis, Basis.self_mem_span_image]
  exact Nat.not_lt_of_ge hi
end LinearStochastic.SpectralNullspace
