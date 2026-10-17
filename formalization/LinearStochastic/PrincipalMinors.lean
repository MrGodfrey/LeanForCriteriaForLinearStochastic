module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section

noncomputable section
namespace LinearStochastic.PrincipalMinors
open scoped BigOperators
open Polynomial Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- All principal minors, including the determinant of the empty submatrix. -/
def AllPrincipalNonneg (M : Matrix ι ι ℝ) : Prop :=
  ∀ s : Finset ι, 0 ≤ (M.submatrix (Subtype.val : s → ι) (Subtype.val : s → ι)).det

omit [Fintype ι] in
theorem psd_principal_nonneg (M : Matrix ι ι ℝ) (hM : M.PosSemidef) :
    AllPrincipalNonneg M := by
  intro s
  exact (hM.submatrix (Subtype.val : s → ι)).det_nonneg

/-- A polynomial with nonnegative coefficients dominates its constant term
at every nonnegative real argument. -/
theorem constant_le_eval (p : ℝ[X]) (hp : ∀ k, 0 ≤ p.coeff k) (t : ℝ) (ht : 0 ≤ t) :
    p.coeff 0 ≤ p.eval t := by
  rw [Polynomial.eval_eq_sum_range]
  simpa only [pow_zero,mul_one] using
    (Finset.single_le_sum (s := Finset.range (p.natDegree+1))
      (f := fun k => p.coeff k*t^k) (fun k _ => mul_nonneg (hp k) (pow_nonneg ht k))
      (show 0 ∈ Finset.range (p.natDegree+1) by simp))

theorem eval_det_one_add (M : Matrix ι ι ℝ) (t : ℝ) :
    (det (1 + (X : ℝ[X]) • M.map C)).eval t = (1 + t • M).det := by
  rw [←Polynomial.coe_evalRingHom,RingHom.map_det]
  congr 1
  ext i j
  change Polynomial.eval t ((1 : Matrix ι ι ℝ[X]) i j + (X : ℝ[X]) * C (M i j)) =
    (1 : Matrix ι ι ℝ) i j + t * M i j
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_C]
  congr 1
  by_cases h : i = j <;> simp [Matrix.one_apply,h]


/-- Nonnegative principal minors force det(I+tM) ≥ 1 for every t ≥ 0. -/
theorem det_one_add_ge_one (M : Matrix ι ι ℝ) (hM : AllPrincipalNonneg M)
    (t : ℝ) (ht : 0 ≤ t) : 1 ≤ (1 + t • M).det := by
  let p := det (1 + (X : ℝ[X]) • M.map C)
  have hc (k : ℕ) : 0 ≤ p.coeff k := by
    rw [Matrix.coeff_det_one_add_X_smul_eq_sum_minors]
    exact Finset.sum_nonneg (fun s _ => hM s)
  have hzero : p.coeff 0 = 1 := by
    rw [Polynomial.coeff_zero_eq_eval_zero,eval_det_one_add]
    simp
  have he := constant_le_eval p hc t ht
  rw [hzero,eval_det_one_add] at he
  exact he

/-- The converse principal-minor criterion is derived from the actual Hermitian
spectrum: a negative eigenvalue would make I+tM singular for a positive t. -/
theorem psd_of_principal_nonneg (M : Matrix ι ι ℝ) (hM : M.IsHermitian)
    (hp : AllPrincipalNonneg M) : M.PosSemidef := by
  apply hM.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  by_contra hn
  have hn' : hM.eigenvalues i < 0 := lt_of_not_ge hn
  let t : ℝ := -(hM.eigenvalues i)⁻¹
  have ht : 0 < t := neg_pos.mpr (inv_lt_zero.mpr hn')
  have hd : 0 < (1 + t • M).det := lt_of_lt_of_le zero_lt_one (det_one_add_ge_one M hp t ht.le)
  have hu : IsUnit (1 + t • M) := ((1 + t • M).isUnit_iff_isUnit_det).mpr (isUnit_iff_ne_zero.mpr hd.ne')
  have he : (1 + t • M).mulVec (hM.eigenvectorBasis i) = 0 := by
    rw [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec,hM.mulVec_eigenvectorBasis,
      smul_smul]
    rw [show (⇑(hM.eigenvectorBasis i) : ι → ℝ) + (t * hM.eigenvalues i) • ⇑(hM.eigenvectorBasis i) =
      (1 + t * hM.eigenvalues i) • ⇑(hM.eigenvectorBasis i) by rw [add_smul,one_smul]]
    have hz : 1 + t * hM.eigenvalues i = 0 := by
      dsimp [t]
      rw [neg_mul,inv_mul_cancel₀ hn'.ne]
      ring
    rw [hz,zero_smul]
  have hz : (⇑(hM.eigenvectorBasis i) : ι → ℝ) = 0 :=
    Matrix.mulVec_injective_of_isUnit hu (he.trans (Matrix.mulVec_zero _).symm)
  have hz' : hM.eigenvectorBasis i = 0 := WithLp.ofLp_injective 2 hz
  have hh := hM.eigenvectorBasis.norm_eq_one i
  rw [hz',norm_zero] at hh
  norm_num at hh

/-- A real symmetric matrix is positive semidefinite exactly when every
principal minor is nonnegative; there is no dimension or invertibility restriction. -/
theorem psd_iff_principal_nonneg (M : Matrix ι ι ℝ) (hM : M.IsSymm) :
    M.PosSemidef ↔ AllPrincipalNonneg M :=
  ⟨psd_principal_nonneg M,psd_of_principal_nonneg M (Matrix.isHermitian_iff_isSymm.mpr hM)⟩

#print axioms psd_iff_principal_nonneg
end LinearStochastic.PrincipalMinors
