module

public import LinearStochastic.SquareSVD
public import LinearStochastic.TallQRElimination

@[expose] public section

/-! Literal selected singular rows and the full O0/O1 staircase subspaces. -/
noncomputable section
namespace LinearStochastic.SVDResidual
open Module
open scoped BigOperators InnerProductSpace
variable {E F X ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [Fintype ι]

/-- Actual selected rows of an orthogonal coordinate transform. -/
def rows (b : OrthonormalBasis ι ℝ F) (s : Set ι) [DecidablePred (· ∈ s)]
    (L : X →ₗ[ℝ] F) : X →ₗ[ℝ] EuclideanSpace ℝ s where
  toFun x := WithLp.toLp 2 (fun i => b.repr (L x) i.val)
  map_add' x y := by ext i; simp
  map_smul' a x := by ext i; simp

omit [FiniteDimensional ℝ F] [FiniteDimensional ℝ X] in
theorem rows_ker (b : OrthonormalBasis ι ℝ F) (s : Set ι) [DecidablePred (· ∈ s)]
    (L : X →ₗ[ℝ] F) : (rows b s L).ker = (Submodule.span ℝ (b '' s))ᗮ.comap L := by
  ext x
  change rows b s L x = 0 ↔ L x ∈ (Submodule.span ℝ (b '' s))ᗮ
  rw [Submodule.mem_orthogonal]
  constructor
  · intro hx y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      have hh := congrArg (fun z : EuclideanSpace ℝ s => z ⟨i, hi⟩) hx
      change b.repr (L x) i = 0 at hh
      simpa only [OrthonormalBasis.repr_apply_apply] using hh
    | zero => simp
    | add y z hy hz ih₁ ih₂ => simp [inner_add_left, ih₁, ih₂]
    | smul a y hy ih => simp [inner_smul_left, ih]
  · intro hx
    ext i
    change b.repr (L x) i.val = 0
    simpa only [OrthonormalBasis.repr_apply_apply] using
      hx (b i.val) (Submodule.subset_span ⟨i.val, i.property, rfl⟩)

omit [FiniteDimensional ℝ X] in
/-- For any actually constructed full left singular basis, the selected zero rows are exact. -/
theorem selected_left_rows (L : X →ₗ[ℝ] F) (M : E →ₗ[ℝ] F)
    (b : OrthonormalBasis ι ℝ F) (s : Set ι) [DecidablePred (· ∈ s)]
    (hs : Submodule.span ℝ (b '' s) = M.adjoint.ker) :
    (rows b s L).ker = feasibleSpace L M := by
  rw [rows_ker, hs, M.adjoint.orthogonal_ker, LinearMap.adjoint_adjoint]
  rfl

omit [FiniteDimensional ℝ X] in
/-- Direct full-left spectral elimination applies also to wide M and never asks for a right factor. -/
theorem wide_or_tall_full_left_rows (L : X →ₗ[ℝ] F) (M : E →ₗ[ℝ] F) :
    (rows (SpectralNullspace.leftBasis M)
      {i : Fin (finrank ℝ F) | finrank ℝ M.range ≤ i.val} L).ker = feasibleSpace L M :=
  selected_left_rows L M _ _ (SpectralNullspace.left_ker_eq_zero_singular_span M).symm

omit [FiniteDimensional ℝ X] in
/-- In the square case the left factor belongs to the proved UΣVᵀ decomposition. -/
theorem square_paired_left_rows (L : X →ₗ[ℝ] F) (M : E →ₗ[ℝ] F)
    (hd : finrank ℝ F = finrank ℝ E) :
    (rows (SquareSVD.leftBasis M hd)
      {i : Fin (finrank ℝ E) | finrank ℝ M.range ≤ i.val} L).ker = feasibleSpace L M :=
  selected_left_rows L M _ _ (SquareSVD.left_ker_eq_zero_span M hd).symm

omit [FiniteDimensional ℝ E] in
/-- Full right singular columns O0 span exactly the retained directions of the algorithm. -/
theorem right_retained_space (R : X →ₗ[ℝ] F) (V : X →ₗᵢ[ℝ] E) :
    (Submodule.span ℝ ((SpectralNullspace.rightBasis R) ''
      {i : Fin (finrank ℝ X) | finrank ℝ R.range ≤ i.val})).map V.toLinearMap =
      (Staircase.retained V R).range := by
  rw [← SpectralNullspace.ker_eq_zero_singular_span, Staircase.retained_range]

/-- The remaining full right singular columns span O1, the removed orthogonal directions. -/
theorem right_positive_span (R : X →ₗ[ℝ] F) :
    Submodule.span ℝ ((SpectralNullspace.rightBasis R) ''
      {i : Fin (finrank ℝ X) | i.val < finrank ℝ R.range}) = R.kerᗮ := by
  have hr : (rows (SpectralNullspace.rightBasis R)
      {i : Fin (finrank ℝ X) | finrank ℝ R.range ≤ i.val} (LinearMap.id : X →ₗ[ℝ] X)).ker =
      R.kerᗮ := by
    rw [rows_ker, ← SpectralNullspace.ker_eq_zero_singular_span]
    rfl
  rw [← hr]
  ext x
  rw [← OrthonormalBasis.coe_toBasis, Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq,
    OrthonormalBasis.coe_toBasis_repr_apply]
  constructor
  · intro hx
    ext i
    change (SpectralNullspace.rightBasis R).repr x i.val = 0
    by_contra hn
    exact Nat.not_lt_of_ge i.property (hx i.val hn)
  · intro hx i hi
    by_contra hn
    have he := congrArg (fun z : EuclideanSpace ℝ
      {i : Fin (finrank ℝ X) | finrank ℝ R.range ≤ i.val} =>
      z ⟨i, Nat.le_of_not_gt hn⟩) hx
    exact hi he

omit [FiniteDimensional ℝ E] in
/-- The spectral O1 update and the existing exact staircase remove the same subspace. -/
theorem right_removed_space (R : X →ₗ[ℝ] F) (V : X →ₗᵢ[ℝ] E) :
    (Submodule.span ℝ ((SpectralNullspace.rightBasis R) ''
      {i : Fin (finrank ℝ X) | i.val < finrank ℝ R.range})).map V.toLinearMap =
      (Staircase.removed V R).range := by
  rw [right_positive_span]
  change _ = (V.toLinearMap.comp (Staircase.frame R.kerᗮ).toLinearMap).range
  rw [LinearMap.range_comp, Staircase.frame_range]

theorem tail_card {n s : ℕ} (hs : s ≤ n) :
    Fintype.card {i : Fin n // s ≤ i.val} = n - s := by
  simpa only [not_lt, Fintype.card_fin, Fintype.card_fin_lt_of_le hs] using
    Fintype.card_subtype_compl (fun i : Fin n => i.val < s)

open TallQRElimination
/-- Actual zero rows from the paired square SVD, concatenated with every bottom QR row. -/
def tallResidual {p h : ℕ} (L : X →ₗ[ℝ] Space p) (M : Space h →ₗ[ℝ] Space p)
    (hp : h ≤ p) :=
  (rows (SquareSVD.leftBasis (triangular M hp) rfl)
    {i : Fin (finrank ℝ (Space h)) | finrank ℝ (triangular M hp).range ≤ i.val}
    (topL L M hp)).prod (bottomL L M)

omit [FiniteDimensional ℝ X] in
theorem tallResidual_ker {p h : ℕ} (L : X →ₗ[ℝ] Space p) (M : Space h →ₗ[ℝ] Space p)
    (hp : h ≤ p) : (tallResidual L M hp).ker = feasibleSpace L M := by
  rw [tallResidual, LinearMap.ker_prod, square_paired_left_rows]
  exact (feasible_top_bottom L M hp).symm

/-- The retained row count is precisely p-rank M, including bottom QR rows. -/
theorem tallResidual_row_count {p h : ℕ} (M : Space h →ₗ[ℝ] Space p) (hp : h ≤ p) :
    Fintype.card {i : Fin (finrank ℝ (Space h)) //
      finrank ℝ (triangular M hp).range ≤ i.val} +
      Fintype.card {j : Fin p // h ≤ j.val} = p - finrank ℝ M.range := by
  rw [tail_card (Submodule.finrank_le _), tail_card hp, triangular_rank M hp]
  have hr : finrank ℝ M.range ≤ h := by
    have hh := Submodule.finrank_le (triangular M hp).range
    rw [triangular_rank M hp] at hh
    simpa [Space] using hh
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin]
  simpa only [add_comm] using Nat.sub_add_sub_cancel hp hr

/-- A wide residual has a nonzero kernel direction absent from its thin right factor. -/
theorem wide_thin_omits_kernel (R : X →ₗ[ℝ] F) (hw : finrank ℝ F < finrank ℝ X) :
    ∃ x : X, x ≠ 0 ∧ R x = 0 ∧
      x ∉ Submodule.span ℝ ((SpectralNullspace.rightBasis R) ''
        {j : Fin (finrank ℝ X) | j.val < finrank ℝ F}) := by
  let i : Fin (finrank ℝ X) := ⟨finrank ℝ F, hw⟩
  refine ⟨SpectralNullspace.rightBasis R i, ?_,
    SpectralNullspace.wide_tail_in_kernel R i le_rfl,
    SpectralNullspace.wide_tail_not_in_thin_span R i le_rfl⟩
  exact (SpectralNullspace.rightBasis R).toBasis.ne_zero i

omit [FiniteDimensional ℝ X] in
/-- When the residual has no rows, its kernel is the entire current coordinate space. -/
theorem empty_rows_ker {κ : Type*} [Fintype κ] [IsEmpty κ]
    (R : X →ₗ[ℝ] EuclideanSpace ℝ κ) : R.ker = ⊤ := by
  have hr : R = 0 := Subsingleton.elim _ _
  rw [hr, LinearMap.ker_zero]
end LinearStochastic.SVDResidual
