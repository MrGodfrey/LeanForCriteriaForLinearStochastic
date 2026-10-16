import LinearStochastic.SpectralNullspace
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! Constructed tall QR, finite Householder realization, and exact residual elimination. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace LinearStochastic.TallQRElimination
open Module InnerProductSpace
open scoped BigOperators
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
variable {p h : ℕ}

def coord (j : Fin p) : Space p →ₗ[ℝ] ℝ where
  toFun x := x j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def top (hp : h ≤ p) : Space p →ₗ[ℝ] Space h where
  toFun x := WithLp.toLp 2 (fun i => x ⟨i.val, lt_of_lt_of_le i.isLt hp⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def bottom : Space p →ₗ[ℝ] EuclideanSpace ℝ {j : Fin p // h ≤ j.val} where
  toFun x := WithLp.toLp 2 (fun j => x j.val)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def paddedColumns (M : Space h →ₗ[ℝ] Space p) (j : Fin p) : Space p :=
  if hj : j.val < h then M (EuclideanSpace.basisFun (Fin h) ℝ ⟨j.val, hj⟩) else 0

def qBasis (M : Space h →ₗ[ℝ] Space p) : OrthonormalBasis (Fin p) ℝ (Space p) :=
  gramSchmidtOrthonormalBasis (by simp [Space]) (paddedColumns M)

def transformed (M : Space h →ₗ[ℝ] Space p) : Space h →ₗ[ℝ] Space p :=
  (qBasis M).repr.toLinearEquiv.toLinearMap.comp M

def triangular (M : Space h →ₗ[ℝ] Space p) (hp : h ≤ p) : Space h →ₗ[ℝ] Space h :=
  (top hp).comp (transformed M)

theorem transformed_column_zero (M : Space h →ₗ[ℝ] Space p) (hp : h ≤ p)
    (i : Fin h) (j : Fin p) (hij : i.val < j.val) :
    transformed M (EuclideanSpace.basisFun (Fin h) ℝ i) j = 0 := by
  have hh := gramSchmidtOrthonormalBasis_inv_triangular'
    (𝕜 := ℝ) (E := Space p) (by simp [Space]) (paddedColumns M)
    (i := ⟨i.val, lt_of_lt_of_le i.isLt hp⟩) (j := j) hij
  change (qBasis M).repr (M (EuclideanSpace.basisFun (Fin h) ℝ i)) j = 0
  simpa only [qBasis, paddedColumns, dif_pos i.isLt] using hh

theorem transformed_bottom_zero (M : Space h →ₗ[ℝ] Space p) (hp : h ≤ p)
    (x : Space h) (j : Fin p) (hj : h ≤ j.val) : transformed M x j = 0 := by
  have hz : (coord j).comp (transformed M) = 0 := by
    apply (EuclideanSpace.basisFun (Fin h) ℝ).toBasis.ext
    intro i
    exact transformed_column_zero M hp i j (lt_of_lt_of_le i.isLt hj)
  exact congrArg (fun f : Space h →ₗ[ℝ] ℝ => f x) hz

theorem triangular_upper (M : Space h →ₗ[ℝ] Space p) (hp : h ≤ p)
    (i j : Fin h) (hij : i < j) :
    triangular M hp (EuclideanSpace.basisFun (Fin h) ℝ i) j = 0 :=
  transformed_column_zero M hp i ⟨j.val, lt_of_lt_of_le j.isLt hp⟩ hij

/-- Full Q is constructed even for rank-deficient M; its transform has a square triangular top. -/
theorem qr_factorization (M : Space h →ₗ[ℝ] Space p) (hp : h ≤ p) (x : Space h) :
    M x = (qBasis M).repr.symm (transformed M x) ∧
      bottom (h := h) (transformed M x) = 0 := by
  refine ⟨(qBasis M).repr.symm_apply_apply (M x) |>.symm, ?_⟩
  ext j
  exact transformed_bottom_zero M hp x j.val j.property

/-- The actual orthogonal QR transform is a product of at most p Householder reflections. -/
theorem qr_householder (M : Space h →ₗ[ℝ] Space p) :
    ∃ l : List (Space p), l.length ≤ p ∧
      (qBasis M).repr = (l.map fun v => Submodule.reflection (ℝ ∙ v)ᗮ).prod := by
  simpa [Space] using (qBasis M).repr.reflections_generate_dim

theorem triangular_ker (M : Space h →ₗ[ℝ] Space p) (hp : h ≤ p) :
    (triangular M hp).ker = M.ker := by
  ext x
  constructor
  · intro hx
    apply (qBasis M).repr.injective
    ext j
    rw [map_zero]
    change transformed M x j = 0
    by_cases hj : j.val < h
    · exact congrArg (fun y : Space h => y ⟨j.val, hj⟩) hx
    · exact transformed_bottom_zero M hp x j (Nat.le_of_not_gt hj)
  · intro hx
    change top hp ((qBasis M).repr (M x)) = 0
    rw [show M x = 0 from hx, map_zero, map_zero]

theorem triangular_rank (M : Space h →ₗ[ℝ] Space p) (hp : h ≤ p) :
    finrank ℝ (triangular M hp).range = finrank ℝ M.range := by
  have h₁ := (triangular M hp).finrank_range_add_finrank_ker
  have h₂ := M.finrank_range_add_finrank_ker
  rw [triangular_ker] at h₁
  omega

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
def topL (L : X →ₗ[ℝ] Space p) (M : Space h →ₗ[ℝ] Space p) (hp : h ≤ p) :
    X →ₗ[ℝ] Space h := (top hp).comp ((qBasis M).repr.toLinearEquiv.toLinearMap.comp L)
def bottomL (L : X →ₗ[ℝ] Space p) (M : Space h →ₗ[ℝ] Space p) :
    X →ₗ[ℝ] EuclideanSpace ℝ {j : Fin p // h ≤ j.val} :=
  bottom.comp ((qBasis M).repr.toLinearEquiv.toLinearMap.comp L)

omit [FiniteDimensional ℝ X] in
/-- Square-top elimination plus the untouched bottom rows is exactly full left-kernel elimination. -/
theorem feasible_top_bottom (L : X →ₗ[ℝ] Space p) (M : Space h →ₗ[ℝ] Space p)
    (hp : h ≤ p) :
    feasibleSpace L M = feasibleSpace (topL L M hp) (triangular M hp) ⊓ (bottomL L M).ker := by
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := (mem_feasibleSpace L M x).mp hx
    refine ⟨(mem_feasibleSpace _ _ _).mpr ⟨a, ?_⟩, ?_⟩
    · change top hp ((qBasis M).repr (L x)) + top hp ((qBasis M).repr (M a)) = 0
      rw [← map_add, ← map_add, ha, map_zero, map_zero]
    · ext j
      have he := congrArg (fun y => (qBasis M).repr y j.val) ha
      simp only [map_add, map_zero, PiLp.add_apply, PiLp.zero_apply] at he
      change (qBasis M).repr (L x) j.val = 0
      have hz := transformed_bottom_zero M hp a j.val j.property
      change (qBasis M).repr (M a) j.val = 0 at hz
      simpa only [hz, add_zero] using he
  · rintro ⟨hx, hb⟩
    obtain ⟨a, ha⟩ := (mem_feasibleSpace _ _ _).mp hx
    apply (mem_feasibleSpace L M x).mpr
    refine ⟨a, (qBasis M).repr.injective ?_⟩
    ext j
    simp only [map_add, map_zero, PiLp.add_apply, PiLp.zero_apply]
    by_cases hj : j.val < h
    · exact congrArg (fun y : Space h => y ⟨j.val, hj⟩) ha
    · have hb' := congrArg (fun y : EuclideanSpace ℝ {j : Fin p // h ≤ j.val} =>
        y ⟨j, Nat.le_of_not_gt hj⟩) hb
      change (qBasis M).repr (L x) j = 0 at hb'
      have hz := transformed_bottom_zero M hp a j (Nat.le_of_not_gt hj)
      change (qBasis M).repr (M a) j = 0 at hz
      rw [hb', hz, add_zero]

/-- Square-top spectral elimination and all bottom rows give the manuscript residual kernel. -/
theorem qr_spectral_residual (L : X →ₗ[ℝ] Space p) (M : Space h →ₗ[ℝ] Space p)
    (hp : h ≤ p) :
    feasibleSpace L M =
      ((SpectralNullspace.leftZeroFrame (triangular M hp)).toLinearMap.adjoint.comp
        (topL L M hp)).ker ⊓ (bottomL L M).ker := by
  exact (feasible_top_bottom L M hp).trans
    (congrArg (fun S : Submodule ℝ X => S ⊓ (bottomL L M).ker)
      (SpectralNullspace.spectral_residual_exact (topL L M hp) (triangular M hp)))
/-- Exact reorthogonalization of a full orthonormal family preserves its given column order. -/
theorem reorthogonalize_ordered (b : OrthonormalBasis (Fin p) ℝ (Space p)) :
    gramSchmidtOrthonormalBasis (by simp [Space]) b = b := by
  apply DFunLike.ext
  intro i
  rw [gramSchmidtOrthonormalBasis_apply_of_orthogonal]
  · simp
  · exact b.orthonormal.2
  · exact b.toBasis.ne_zero i
end LinearStochastic.TallQRElimination
