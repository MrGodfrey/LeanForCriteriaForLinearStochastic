module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-! Literal singular-value threshold contract. This is the mathematical
numerical-rank rule, not a theorem that floating-point outputs certify exact
rank or controllability. Its zero-tolerance and possible-disagreement behavior
are proved with the actual singular values, not a supplied spectrum. -/
noncomputable section
namespace LinearStochastic.NumericalRank
open Module
open scoped NNReal
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def threshold (T : E →ₗ[ℝ] F) (τabs τrel : ℝ≥0) : ℝ :=
  τabs + τrel * ‖T.toContinuousLinearMap‖

def rank (T : E →ₗ[ℝ] F) (τabs τrel : ℝ≥0) : ℕ :=
  (T.singularValues.support.filter (fun i => threshold T τabs τrel < T.singularValues i)).card

omit [FiniteDimensional ℝ F] in
theorem threshold_nonneg (T : E →ₗ[ℝ] F) (τabs τrel : ℝ≥0) :
    0 ≤ threshold T τabs τrel := by unfold threshold; positivity

/-- Restricting to positive singular values does not lose any value exceeding
the nonnegative threshold; all remaining singular values are exactly zero. -/
theorem selected_iff (T : E →ₗ[ℝ] F) (τabs τrel : ℝ≥0) (i : ℕ) :
    i ∈ T.singularValues.support.filter (fun j => threshold T τabs τrel < T.singularValues j) ↔
      threshold T τabs τrel < T.singularValues i := by
  simp only [Finset.mem_filter,Finsupp.mem_support_iff,and_iff_right_iff_imp]
  exact fun h => ne_of_gt ((threshold_nonneg T τabs τrel).trans_lt h)

theorem le_exact_rank (T : E →ₗ[ℝ] F) (τabs τrel : ℝ≥0) :
    rank T τabs τrel ≤ finrank ℝ T.range := by
  rw [rank,←T.card_support_singularValues]
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem zero_tolerance (T : E →ₗ[ℝ] F) : rank T 0 0 = finrank ℝ T.range := by
  rw [rank,←T.card_support_singularValues]
  congr 1
  apply Finset.filter_eq_self.mpr
  intro i hi
  simpa [threshold] using (T.singularValues_pos_iff_ne_zero i).mpr (Finsupp.mem_support_iff.mp hi)

theorem monotone_tolerances (T : E →ₗ[ℝ] F) {a b c d : ℝ≥0} (ha : a ≤ c) (hb : b ≤ d) :
    rank T c d ≤ rank T a b := by
  apply Finset.card_le_card
  intro i hi
  rw [selected_iff] at hi ⊢
  apply lt_of_le_of_lt ?_ hi
  exact add_le_add (NNReal.coe_le_coe.mpr ha)
    (mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr hb) (norm_nonneg _))

/-- A positive threshold can destroy a genuine nonzero rank: choosing the
actual largest singular value as the absolute tolerance counts no directions. -/
theorem positive_threshold_can_disagree (T : E →ₗ[ℝ] F) (hT : T ≠ 0) :
    ∃ τabs : ℝ≥0, 0 < τabs ∧ rank T τabs 0 = 0 ∧ 0 < finrank ℝ T.range := by
  have hr : 0 < finrank ℝ T.range := by
    by_contra! hr
    have hz : T.singularValues = 0 := by
      ext i
      apply T.singularValues_eq_zero_iff_le_finrank_range.mpr
      omega
    exact hT (T.singularValues_eq_zero_iff.mp hz)
  let τabs : ℝ≥0 := ⟨T.singularValues 0,T.singularValues_nonneg 0⟩
  refine ⟨τabs,(T.singularValues_pos_iff_lt_finrank_range).mpr hr,?_,hr⟩
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  rw [selected_iff] at hi
  have hh := T.singularValues_antitone (show 0 ≤ i from Nat.zero_le i)
  have he : threshold T τabs 0 = T.singularValues 0 := by simp only [threshold,NNReal.coe_zero,zero_mul,add_zero]; rfl
  rw [he] at hi
  exact (not_lt_of_ge hh) hi

/-- The manuscript formula specialized to the actual Euclidean matrix operator. -/
def matrixRank {n r : ℕ} (X : Matrix (Fin n) (Fin r) ℝ) (τabs τrel : ℝ≥0) : ℕ :=
  rank X.toEuclideanLin τabs τrel

end LinearStochastic.NumericalRank
