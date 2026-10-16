import LinearStochastic.AlgebraExamples
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ClusterPt

/-!
# Continuous full-rank tests cannot characterize the manuscript's vanishing flag

The obstruction is proved for the actual coefficient family, without assuming
any stochastic controllability classification. It therefore becomes the
corresponding controllability obstruction only after that classification is proved.
-/
noncomputable section
namespace LinearStochastic.NonrobustTopology
open Module

/-- Full row rank is precisely linear independence of the actual matrix rows. -/
theorem full_row_rank_iff {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) :
    M.rank = a ↔ LinearIndependent ℝ M.row := by
  rw [linearIndependent_iff_card_eq_finrank_span, M.rank_eq_finrank_span_row]
  simp only [Fintype.card_fin, Set.finrank]
  exact eq_comm

/-- Full row rank is open in the ordinary entrywise matrix topology. -/
theorem isOpen_full_row_rank (a b : ℕ) :
    IsOpen {M : Matrix (Fin a) (Fin b) ℝ | M.rank = a} := by
  simp only [full_row_rank_iff]
  exact isOpen_setOfPred_linearIndependent

/-- Maximal rank of a fixed-size real matrix is an open condition, for either shape. -/
theorem isOpen_maximal_rank (a b : ℕ) :
    IsOpen {M : Matrix (Fin a) (Fin b) ℝ | M.rank = min a b} := by
  by_cases h : a ≤ b
  · simpa only [min_eq_left h] using isOpen_full_row_rank a b
  · have hc : Continuous (fun M : Matrix (Fin a) (Fin b) ℝ => M.transpose) :=
      continuous_pi fun i => continuous_pi fun j => (continuous_apply i).comp (continuous_apply j)
    have ho := (isOpen_full_row_rank b a).preimage hc
    simpa only [Set.preimage_ofPred_eq, Matrix.rank_transpose, min_eq_right (le_of_not_ge h)] using ho

/-- Along the actual manuscript family, a vanishing stable flag occurs exactly at zero. -/
theorem actual_flag_bot_iff (m : ℕ) (ε : ℝ) :
    (Examples.Nonrobustness.coefficients m ε).flag 2 = ⊥ ↔ ε = 0 := by
  by_cases h : ε = 0
  · subst ε
    exact ⟨fun _ => rfl, fun _ => Examples.Nonrobustness.flag_two_zero m⟩
  · rw [Examples.Nonrobustness.flag_two_ne_zero m ε h]
    have hn : Examples.Nonrobustness.firstAxis ≠ ⊥ := by
      intro hz
      have hd := Examples.Nonrobustness.firstAxis_finrank
      rw [hz, finrank_bot] at hd
      omega
    simp [hn, h]

/-- The actual zero-flag property is not open even along this one-dimensional family. -/
theorem actual_flag_not_open (m : ℕ) :
    ¬IsOpen {ε : ℝ | (Examples.Nonrobustness.coefficients m ε).flag 2 = ⊥} := by
  simpa only [actual_flag_bot_iff, Set.ofPred_eq_eq_singleton] using not_isOpen_singleton (0 : ℝ)

/-- No continuous fixed-size matrix on this real parameter can characterize the actual flag
by maximal rank. The statement includes zero-size and tall/wide matrices. -/
theorem no_continuous_maximal_rank_test (m a b : ℕ)
    (M : ℝ → Matrix (Fin a) (Fin b) ℝ) (hM : Continuous M) :
    ¬ (∀ ε, (M ε).rank = min a b ↔
      (Examples.Nonrobustness.coefficients m ε).flag 2 = ⊥) := by
  intro h
  have ho := (isOpen_maximal_rank a b).preimage hM
  apply actual_flag_not_open m
  simpa only [Set.preimage_ofPred_eq, h] using ho

/-- The usual finite-dimensional space of all original matrix coefficients. -/
abbrev CoefficientSpace (n r m : ℕ) :=
  Matrix (Fin n) (Fin n) ℝ × Matrix (Fin n) (Fin r) ℝ ×
    (Fin m → Matrix (Fin n) (Fin n) ℝ) × (Fin m → Matrix (Fin n) (Fin r) ℝ)

/-- The manuscript's complete coefficient tuple, including its zero diffusion-control part. -/
def coefficientFamily (m : ℕ) (ε : ℝ) : CoefficientSpace 2 1 (m+1) :=
  (Examples.Nonrobustness.A, Examples.Nonrobustness.B, Examples.Nonrobustness.C m ε,
    fun _ => 0)

/-- This really is a continuous perturbation of the original coefficients. -/
theorem coefficientFamily_continuous (m : ℕ) : Continuous (coefficientFamily m) := by
  have hc : Continuous (Examples.Nonrobustness.C m) := by
    apply continuous_pi
    intro j
    by_cases hj : j = 0
    · simp only [Examples.Nonrobustness.C, hj, if_true]
      exact continuous_id.smul continuous_const
    · simp only [Examples.Nonrobustness.C, hj, if_false]
      exact continuous_const
  exact continuous_const.prodMk (continuous_const.prodMk (hc.prodMk continuous_const))

/-- The vanishing-flag locus is not open in the full space of original coefficients. -/
theorem actual_coefficient_flag_not_open (m : ℕ) :
    ¬IsOpen {s : CoefficientSpace 2 1 (m+1) |
      (AdjointCoefficients.fromMatrices s.1 s.2.1 s.2.2.1 s.2.2.2).flag 2 = ⊥} := by
  intro h
  exact actual_flag_not_open m (h.preimage (coefficientFamily_continuous m))

/-- No single continuous map from the actual coefficient matrices to any fixed-size
matrix can detect vanishing stable flag by maximal rank on all systems of these dimensions. -/
theorem no_continuous_coefficient_rank_test (m a b : ℕ)
    (M : CoefficientSpace 2 1 (m+1) → Matrix (Fin a) (Fin b) ℝ) (hM : Continuous M) :
    ¬ (∀ s, (M s).rank = min a b ↔
      (AdjointCoefficients.fromMatrices s.1 s.2.1 s.2.2.1 s.2.2.2).flag 2 = ⊥) := by
  intro h
  apply no_continuous_maximal_rank_test m a b (M ∘ coefficientFamily m)
    (hM.comp (coefficientFamily_continuous m))
  intro ε
  exact h (coefficientFamily m ε)

/-- The actual prescribed finite matrix pair at step two, followed by its rank difference. -/
def actualRankDifference (m : ℕ) (ε : ℝ) : ℕ :=
  let p := Coordinates.finitePair Examples.Nonrobustness.A Examples.Nonrobustness.B
    (Examples.Nonrobustness.C m ε)
    (fun _ : Fin (m+1) => (0 : Matrix (Fin 2) (Fin 1) ℝ)) 1
  (Matrix.fromCols p.2 p.1).rank - p.2.rank

/-- The prescribed rank-difference test is exactly the singleton {0} along this family. -/
theorem actual_rank_difference_iff (m : ℕ) (ε : ℝ) :
    actualRankDifference m ε = 2 ↔ ε = 0 := by
  by_cases h : ε = 0
  · subst ε
    exact ⟨fun _ => rfl, fun _ => Examples.Nonrobustness.finitePair_delta_two_zero m⟩
  · have hh : actualRankDifference m ε = 1 :=
      Examples.Nonrobustness.finitePair_delta_two_ne_zero m ε h
    simp [hh, h]

/-- The actual polynomial rank-difference criterion is not open along the coefficient family. -/
theorem actual_rank_difference_not_open (m : ℕ) :
    ¬IsOpen {ε : ℝ | actualRankDifference m ε = 2} := by
  simpa only [actual_rank_difference_iff, Set.ofPred_eq_eq_singleton] using
    not_isOpen_singleton (0 : ℝ)

/-- The corresponding rank-difference test is also nonopen in the full coefficient space. -/
theorem actual_coefficient_rank_difference_not_open (m : ℕ) :
    ¬IsOpen {s : CoefficientSpace 2 1 (m+1) |
      (let p := Coordinates.finitePair s.1 s.2.1 s.2.2.1 s.2.2.2 1;
        (Matrix.fromCols p.2 p.1).rank - p.2.rank) = 2} := by
  intro h
  exact actual_rank_difference_not_open m (h.preimage (coefficientFamily_continuous m))

#print axioms actual_coefficient_flag_not_open
#print axioms actual_coefficient_rank_difference_not_open
#print axioms no_continuous_coefficient_rank_test
#print axioms actual_rank_difference_not_open
#print axioms isOpen_maximal_rank
#print axioms no_continuous_maximal_rank_test
end LinearStochastic.NonrobustTopology
