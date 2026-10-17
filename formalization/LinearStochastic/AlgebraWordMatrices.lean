module

public import LinearStochastic.AlgebraCoordinates
public import LinearStochastic.AlgebraWords

@[expose] public section

/-!
# The exact finite word matrices H₀,...,Hₙ₋₁

There are no duplicate short-word columns in `wordMatrix`: stage k contains
exactly k generators followed by H. `cumulativeMatrix` concatenates these
stages in order. Taking q=m+1 and M=(E₁,...,Eₘ,F) gives (eq:word-blocks).
-/
noncomputable section
namespace LinearStochastic.WordMatrices
open Module
open scoped BigOperators

/-- Columns of Hₖ, with the newest left factor first. -/
def WordIndex (r q : ℕ) : ℕ → Type
  | 0 => Fin r
  | k + 1 => Fin q × WordIndex r q k

instance wordIndexFintype (r q : ℕ) : (k : ℕ) → Fintype (WordIndex r q k)
  | 0 => inferInstanceAs (Fintype (Fin r))
  | k + 1 => letI := wordIndexFintype r q k
             inferInstanceAs (Fintype (Fin q × WordIndex r q k))

/-- Columns of [H₀ ... Hₖ]. -/
def CumulativeIndex (r q : ℕ) : ℕ → Type
  | 0 => Fin r
  | k + 1 => CumulativeIndex r q k ⊕ WordIndex r q (k + 1)

instance cumulativeIndexFintype (r q : ℕ) : (k : ℕ) → Fintype (CumulativeIndex r q k)
  | 0 => inferInstanceAs (Fintype (Fin r))
  | k + 1 => letI := cumulativeIndexFintype r q k
             inferInstanceAs (Fintype (CumulativeIndex r q k ⊕ WordIndex r q (k + 1)))

variable {n r q : ℕ}

/-- H₀=H, Hₖ₊₁=[M₁Hₖ ... M_qHₖ], as literal matrices. -/
def wordMatrix (M : Fin q → Matrix (Fin n) (Fin n) ℝ) (H : Matrix (Fin n) (Fin r) ℝ) :
    (k : ℕ) → Matrix (Fin n) (WordIndex r q k) ℝ
  | 0 => H
  | k + 1 => Coordinates.joint (fun i => M i * wordMatrix M H k)

/-- Literal horizontal concatenation of H₀,...,Hₖ. -/
def cumulativeMatrix (M : Fin q → Matrix (Fin n) (Fin n) ℝ) (H : Matrix (Fin n) (Fin r) ℝ) :
    (k : ℕ) → Matrix (Fin n) (CumulativeIndex r q k) ℝ
  | 0 => H
  | k + 1 => Matrix.fromCols (cumulativeMatrix M H k) (wordMatrix M H (k + 1))

theorem wordIndex_card (r q k : ℕ) : Fintype.card (WordIndex r q k) = r * q ^ k := by
  induction k with
  | zero =>
    change Fintype.card (Fin r) = r * q ^ 0
    simp
  | succ k ih =>
    change Fintype.card (Fin q × WordIndex r q k) = _
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
    ring

theorem cumulativeIndex_card (r q k : ℕ) :
    Fintype.card (CumulativeIndex r q k) = r * ∑ j ∈ Finset.range (k + 1), q ^ j := by
  induction k with
  | zero =>
    change Fintype.card (Fin r) = r * ∑ j ∈ Finset.range (0 + 1), q ^ j
    simp
  | succ k ih =>
    change Fintype.card (CumulativeIndex r q k ⊕ WordIndex r q (k + 1)) = _
    rw [Fintype.card_sum, ih, wordIndex_card, Finset.sum_range_succ (fun j => q ^ j) (k + 1)]
    ring

variable {α β ρ : Type*}

/-- Range of a finite horizontal family is the sum of all of its ranges. -/
theorem range_joint [Fintype α] (P : Fin q → Matrix ρ α ℝ) :
    (Coordinates.joint P).mulVecLin.range = ⨆ i, (P i).mulVecLin.range := by
  classical
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    change (Coordinates.joint P).mulVec a ∈ _
    rw [Coordinates.joint_mulVec]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.mem_iSup_of_mem i ⟨fun j => a (i, j), rfl⟩
  · refine iSup_le fun i => ?_
    rintro x ⟨v, rfl⟩
    refine ⟨fun p => if p.1 = i then v p.2 else 0, ?_⟩
    change (Coordinates.joint P).mulVec _ = (P i).mulVec v
    rw [Coordinates.joint_mulVec, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp only [hj, ite_false]
      exact Matrix.mulVec_zero _
    · simp

/-- Range of a binary horizontal concatenation is the sum of the two ranges. -/
theorem range_fromCols [Fintype α] [Fintype β]
    (P : Matrix ρ α ℝ) (Q : Matrix ρ β ℝ) :
    (Matrix.fromCols P Q).mulVecLin.range = P.mulVecLin.range ⊔ Q.mulVecLin.range := by
  have h : (Matrix.fromCols P Q).mulVecLin.range = (P.mulVecLin.coprod Q.mulVecLin).range := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨(a ∘ Sum.inl, a ∘ Sum.inr), (Matrix.fromCols_mulVec P Q a).symm⟩
    · rintro ⟨⟨a, v⟩, rfl⟩
      exact ⟨Sum.elim a v, Matrix.fromCols_mulVec_sumElim P Q a v⟩
  rw [h, LinearMap.range_coprod]

/-- The actual Hₖ matrix has exactly the kth word layer as its column space. -/
theorem wordMatrix_range (M : Fin q → Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin n) (Fin r) ℝ) (k : ℕ) :
    (wordMatrix M H k).mulVecLin.range =
      Words.layer (fun i => (M i).mulVecLin) H.mulVecLin.range k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (Coordinates.joint (fun i => M i * wordMatrix M H k)).mulVecLin.range = _
    rw [range_joint, Words.layer_succ]
    apply iSup_congr
    intro i
    rw [Matrix.mulVecLin_mul, LinearMap.range_comp, ih]

/-- The displayed concatenation spans exactly all words of length at most k. -/
theorem cumulativeMatrix_range (M : Fin q → Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin n) (Fin r) ℝ) (k : ℕ) :
    (cumulativeMatrix M H k).mulVecLin.range =
      Words.wordSpan (fun i => (M i).mulVecLin) H.mulVecLin.range k := by
  suffices hc : (cumulativeMatrix M H k).mulVecLin.range =
      Words.cumulative (fun i => (M i).mulVecLin) H.mulVecLin.range k by
    rw [hc, Words.cumulative_eq_reach, Words.reach_eq_wordSpan]
  induction k with
  | zero => rfl
  | succ k ih =>
    change (Matrix.fromCols (cumulativeMatrix M H k) (wordMatrix M H (k + 1))).mulVecLin.range = _
    rw [range_fromCols, Words.cumulative_succ, ih, wordMatrix_range]

/-- Full rank of the literal concatenation is equivalent to the whole word envelope. -/
theorem cumulativeMatrix_full_rank_iff (M : Fin q → Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin n) (Fin r) ℝ) (k : ℕ) :
    (cumulativeMatrix M H k).rank = n ↔
      Words.wordSpan (fun i => (M i).mulVecLin) H.mulVecLin.range k = ⊤ := by
  rw [Matrix.rank, cumulativeMatrix_range]
  constructor
  · intro h
    exact Submodule.eq_top_of_finrank_eq (by simpa using h)
  · intro h
    rw [h, finrank_top]
    simp

/-- At n−1 factors, these actual matrix columns are the smallest invariant envelope. -/
theorem cumulativeMatrix_finite_envelope (M : Fin q → Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin n) (Fin r) ℝ) :
    Words.Invariant (fun i => (M i).mulVecLin) (cumulativeMatrix M H (n - 1)).mulVecLin.range ∧
    H.mulVecLin.range ≤ (cumulativeMatrix M H (n - 1)).mulVecLin.range ∧
    (∀ U, H.mulVecLin.range ≤ U → Words.Invariant (fun i => (M i).mulVecLin) U →
      (cumulativeMatrix M H (n - 1)).mulVecLin.range ≤ U) := by
  rw [cumulativeMatrix_range]
  simpa using Words.finite_word_envelope (fun i => (M i).mulVecLin) H.mulVecLin.range

#print axioms cumulativeMatrix_range
#print axioms cumulativeMatrix_finite_envelope
end LinearStochastic.WordMatrices
