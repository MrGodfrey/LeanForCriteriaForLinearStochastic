import LinearStochastic.AlgebraBlocks

/-!
# Literal coordinate matrices for the rank theorem

The finite sum/product index types retain the exact row/column block order.
`matrixPair k` is the manuscript pair `(K_{k+1},N_{k+1})`. All products and
Kronecker blocks below are actual Mathlib matrices, not abstract placeholders.
-/
noncomputable section
namespace LinearStochastic
namespace Coordinates
open Module
open scoped BigOperators

/-- Ordered row blocks: r, then m copies of the old rows, then old rows. -/
def RowIndex (r m : ℕ) : ℕ → Type
  | 0 => Fin r
  | k + 1 => Fin r ⊕ ((Fin m × RowIndex r m k) ⊕ RowIndex r m k)

/-- Ordered column blocks: mn, then m copies of old columns, then old columns. -/
def AuxIndex (n m : ℕ) : ℕ → Type
  | 0 => Fin m × Fin n
  | k + 1 => (Fin m × Fin n) ⊕ ((Fin m × AuxIndex n m k) ⊕ AuxIndex n m k)

instance rowIndexFintype (r m : ℕ) : (k : ℕ) → Fintype (RowIndex r m k)
  | 0 => inferInstanceAs (Fintype (Fin r))
  | k + 1 => letI := rowIndexFintype r m k
             inferInstanceAs (Fintype (Fin r ⊕ ((Fin m × RowIndex r m k) ⊕ RowIndex r m k)))

instance auxIndexFintype (n m : ℕ) : (k : ℕ) → Fintype (AuxIndex n m k)
  | 0 => inferInstanceAs (Fintype (Fin m × Fin n))
  | k + 1 => letI := auxIndexFintype n m k
             inferInstanceAs (Fintype ((Fin m × Fin n) ⊕
               ((Fin m × AuxIndex n m k) ⊕ AuxIndex n m k)))

variable {n r m : ℕ} {ρ α σ : Type*}

/-- Horizontal concatenation of m coefficient matrices. -/
def joint (M : Fin m → Matrix ρ σ ℝ) : Matrix ρ (Fin m × σ) ℝ :=
  fun i j => M j.1 i j.2

theorem joint_mulVec [Fintype σ] (M : Fin m → Matrix ρ σ ℝ)
    (w : (Fin m × σ) → ℝ) :
    (joint M).mulVec w = ∑ j, (M j).mulVec (fun i => w (j, i)) := by
  ext i
  simp [joint, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

theorem identity_kronecker_mulVec [Fintype σ]
    (M : Matrix ρ σ ℝ) (w : (Fin m × σ) → ℝ) (i : Fin m) (a : ρ) :
    (Matrix.kroneckerMap (fun x y : ℝ => x * y)
      (1 : Matrix (Fin m) (Fin m) ℝ) M).mulVec w (i, a) =
      M.mulVec (fun b => w (i, b)) a := by
  simp [Matrix.mulVec, dotProduct, Matrix.kroneckerMap, Matrix.one_apply,
    Fintype.sum_prod_type]

/-- Literal column of three blocks Bᵀ, 0, K Aᵀ. -/
def nextK (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (K : Matrix ρ (Fin n) ℝ) : Matrix (Fin r ⊕ ((Fin m × ρ) ⊕ ρ)) (Fin n) ℝ :=
  Matrix.fromRows B.transpose (Matrix.fromRows 0 (K * A.transpose))

/-- Literal three-by-three matrix in paper (eq:pair), including both Iₘ⊗ blocks. -/
def nextN [Fintype α]
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (K : Matrix ρ (Fin n) ℝ) (N : Matrix ρ α ℝ) :
    Matrix (Fin r ⊕ ((Fin m × ρ) ⊕ ρ))
      ((Fin m × Fin n) ⊕ ((Fin m × α) ⊕ α)) ℝ :=
  Matrix.fromRows
    (Matrix.fromCols (joint (fun j => (D j).transpose)) (Matrix.fromCols 0 0))
    (Matrix.fromRows
      (Matrix.fromCols ((1 : Matrix (Fin m) (Fin m) ℝ).kronecker K)
        (Matrix.fromCols ((1 : Matrix (Fin m) (Fin m) ℝ).kronecker N) 0))
      (Matrix.fromCols (K * joint (fun j => (C j).transpose)) (Matrix.fromCols 0 N)))

/-- Exact action of the three-by-three block pair on its coordinate vectors. -/
theorem next_action [Fintype α]
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (K : Matrix ρ (Fin n) ℝ) (N : Matrix ρ α ℝ)
    (v : Fin n → ℝ) (a : ((Fin m × Fin n) ⊕ ((Fin m × α) ⊕ α)) → ℝ) :
    (nextK A B K).mulVec v + (nextN C D K N).mulVec a =
    Sum.elim
      (B.transpose.mulVec v + ∑ j, (D j).transpose.mulVec (fun i => a (.inl (j, i))))
      (Sum.elim
        (fun p => (K.mulVec (fun i => a (.inl (p.1, i))) +
          N.mulVec (fun i => a (.inr (.inl (p.1, i))))) p.2)
        (K.mulVec (A.transpose.mulVec v +
          ∑ j, (C j).transpose.mulVec (fun i => a (.inl (j, i)))) +
          N.mulVec (fun i => a (.inr (.inr i))))) := by
  ext i
  rcases i with i | (⟨j, i⟩ | i)
  · simp [nextK, nextN, -Matrix.fromRows_fromCols_eq_fromBlocks, joint_mulVec, Function.comp_def]
  · simp [nextK, nextN, -Matrix.fromRows_fromCols_eq_fromBlocks, identity_kronecker_mulVec, Function.comp_def]
  · simp [nextK, nextN, -Matrix.fromRows_fromCols_eq_fromBlocks, ← Matrix.mulVec_mulVec, joint_mulVec, Matrix.mulVec_add,
      Function.comp_def, add_assoc]

/-- Recursively constructed polynomial matrices of the paper. -/
def matrixPair
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    (k : ℕ) → Matrix (RowIndex r m k) (Fin n) ℝ ×
      Matrix (RowIndex r m k) (AuxIndex n m k) ℝ
  | 0 => (B.transpose, joint (fun j => (D j).transpose))
  | k + 1 =>
    let p := matrixPair A B C D k
    (nextK A B p.1, nextN C D p.1 p.2)

/-- Every existential block equation is exactly the recursively defined obstruction. -/
theorem matrixPair_feasible_iff
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin m → Matrix (Fin n) (Fin r) ℝ) (k : ℕ) (v : Fin n → ℝ) :
    (∃ a, (matrixPair A B C D k).1.mulVec v +
      (matrixPair A B C D k).2.mulVec a = 0) ↔
      v ∈ (AdjointCoefficients.fromMatrices A B C D).flag (k + 1) := by
  let s := AdjointCoefficients.fromMatrices A B C D
  induction k generalizing v with
  | zero =>
    change (∃ a, B.transpose.mulVec v + (joint (fun j => (D j).transpose)).mulVec a = 0) ↔
      v ∈ s.obstruction (⊤ : Submodule ℝ (Fin n → ℝ))
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨Submodule.mem_top, fun j i => a (j, i), fun _ => Submodule.mem_top, ?_, Submodule.mem_top⟩
      simpa [s, AdjointCoefficients.fromMatrices, Matrix.toLin'_apply, joint_mulVec] using ha
    · rintro ⟨_, w, _, hB, _⟩
      refine ⟨fun p => w p.1 p.2, ?_⟩
      simpa [s, AdjointCoefficients.fromMatrices, Matrix.toLin'_apply, joint_mulVec] using hB
  | succ k ih =>
    let p := matrixPair A B C D k
    change (∃ a, (nextK A B p.1).mulVec v + (nextN C D p.1 p.2).mulVec a = 0) ↔
      v ∈ s.flag ((k + 1) + 1)
    constructor
    · rintro ⟨a, ha⟩
      have hh := (next_action A B C D p.1 p.2 v a).symm.trans ha
      let w : Fin m → Fin n → ℝ := fun j i => a (.inl (j, i))
      let α : Fin m → AuxIndex n m k → ℝ := fun j i => a (.inr (.inl (j, i)))
      let β : AuxIndex n m k → ℝ := fun i => a (.inr (.inr i))
      have hB : B.transpose.mulVec v + ∑ j, (D j).transpose.mulVec (w j) = 0 :=
        funext (fun i => congrFun hh (.inl i))
      have hw : ∀ j, p.1.mulVec (w j) + p.2.mulVec (α j) = 0 :=
        fun j => funext (fun i => congrFun hh (.inr (.inl (j, i))))
      have hA : p.1.mulVec (A.transpose.mulVec v + ∑ j, (C j).transpose.mulVec (w j)) +
          p.2.mulVec β = 0 := funext (fun i => congrFun hh (.inr (.inr i)))
      apply s.flag_mem_of_constraints (k + 1) v w
      · intro j
        exact (ih (w j)).mp ⟨α j, hw j⟩
      · simpa [s, AdjointCoefficients.fromMatrices, Matrix.toLin'_apply] using hB
      · have hm := (ih (A.transpose.mulVec v + ∑ j, (C j).transpose.mulVec (w j))).mp ⟨β, hA⟩
        simpa [s, AdjointCoefficients.fromMatrices, Matrix.toLin'_apply] using hm
    · rintro ⟨_, w, hw, hB, hA⟩
      have hα : ∀ j, ∃ a, p.1.mulVec (w j) + p.2.mulVec a = 0 :=
        fun j => (ih (w j)).mpr (hw j)
      choose α hα using hα
      have hm : A.transpose.mulVec v + ∑ j, (C j).transpose.mulVec (w j) ∈ s.flag (k + 1) := by
        change s.A v + ∑ j, s.C j (w j) ∈ s.flag (k + 1) at hA
        simpa only [s, AdjointCoefficients.fromMatrices, Matrix.toLin'_apply] using hA
      obtain ⟨β, hβ⟩ := (ih _).mpr hm
      refine ⟨Sum.elim (fun p => w p.1 p.2) (Sum.elim (fun p => α p.1 p.2) β), ?_⟩
      apply (next_action A B C D p.1 p.2 v _).trans
      ext i
      rcases i with i | (⟨j, i⟩ | i)
      · change (B.transpose.mulVec v + ∑ j, (D j).transpose.mulVec (w j)) i = 0
        exact congrFun hB i
      · exact congrFun (hα j) i
      · exact congrFun hβ i

/-- The horizontal concatenation has exactly the range of the corresponding coprod map. -/
theorem range_fromCols [Fintype α]
    (K : Matrix ρ (Fin n) ℝ) (N : Matrix ρ α ℝ) :
    (Matrix.fromCols N K).mulVecLin.range = (N.mulVecLin.coprod K.mulVecLin).range := by
  ext y
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨(a ∘ Sum.inl, a ∘ Sum.inr), ?_⟩
    exact (Matrix.fromCols_mulVec N K a).symm
  · rintro ⟨⟨a, v⟩, rfl⟩
    exact ⟨Sum.elim a v, Matrix.fromCols_mulVec_sumElim N K a v⟩

/-- Matrix.rank, not an assumed abstract rank, obeys the proved codimension identity. -/
theorem matrix_rank_difference [Fintype ρ] [Fintype α]
    (K : Matrix ρ (Fin n) ℝ) (N : Matrix ρ α ℝ) :
    (Matrix.fromCols N K).rank - N.rank =
      n - finrank ℝ (feasibleSpace K.mulVecLin N.mulVecLin) := by
  rw [Matrix.rank, range_fromCols, Matrix.rank]
  simpa using rank_difference_eq_codimension K.mulVecLin N.mulVecLin

/-- Full matrix form of paper (eq:rank-codimension). -/
theorem matrixPair_rank_codimension
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin m → Matrix (Fin n) (Fin r) ℝ) (k : ℕ) :
    (Matrix.fromCols (matrixPair A B C D k).2 (matrixPair A B C D k).1).rank -
      (matrixPair A B C D k).2.rank =
      n - finrank ℝ ((AdjointCoefficients.fromMatrices A B C D).flag (k + 1)) := by
  rw [matrix_rank_difference]
  have hspace : feasibleSpace (matrixPair A B C D k).1.mulVecLin
      (matrixPair A B C D k).2.mulVecLin =
      (AdjointCoefficients.fromMatrices A B C D).flag (k + 1) := by
    ext v
    rw [mem_feasibleSpace]
    exact matrixPair_feasible_iff A B C D k v
  rw [hspace]

/-- The manuscript's a_{k+1}. -/
def rowWidth (r m k : ℕ) : ℕ := r * ∑ l ∈ Finset.range (k + 1), (m + 1) ^ l

/-- The manuscript's b_{k+1}. -/
def auxWidth (n m k : ℕ) : ℕ := (m * n) * ∑ l ∈ Finset.range (k + 1), (m + 1) ^ l

@[simp] theorem rowWidth_zero (r m : ℕ) : rowWidth r m 0 = r := by simp [rowWidth]
@[simp] theorem auxWidth_zero (n m : ℕ) : auxWidth n m 0 = m * n := by simp [auxWidth]

theorem rowWidth_succ (r m k : ℕ) :
    rowWidth r m (k + 1) = r + (m * rowWidth r m k + rowWidth r m k) := by
  simp only [rowWidth, geom_sum_succ (n := k + 1)]
  ring

theorem auxWidth_succ (n m k : ℕ) :
    auxWidth n m (k + 1) = m * n + (m * auxWidth n m k + auxWidth n m k) := by
  simp only [auxWidth, geom_sum_succ (n := k + 1)]
  ring

/-- Canonical flattening in the displayed order: first block, repeated blocks, last block. -/
def rowIndexEquivFin (r m : ℕ) : (k : ℕ) → RowIndex r m k ≃ Fin (rowWidth r m k)
  | 0 => finCongr (rowWidth_zero r m).symm
  | k + 1 =>
    (Equiv.sumCongr (Equiv.refl (Fin r))
      ((Equiv.sumCongr
        ((Equiv.prodCongr (Equiv.refl (Fin m)) (rowIndexEquivFin r m k)).trans finProdFinEquiv)
        (rowIndexEquivFin r m k)).trans finSumFinEquiv)).trans
      (finSumFinEquiv.trans (finCongr (rowWidth_succ r m k).symm))

/-- Canonical flattening of the witness blocks in the manuscript's order. -/
def auxIndexEquivFin (n m : ℕ) : (k : ℕ) → AuxIndex n m k ≃ Fin (auxWidth n m k)
  | 0 => finProdFinEquiv.trans (finCongr (auxWidth_zero n m).symm)
  | k + 1 =>
    (Equiv.sumCongr finProdFinEquiv
      ((Equiv.sumCongr
        ((Equiv.prodCongr (Equiv.refl (Fin m)) (auxIndexEquivFin n m k)).trans finProdFinEquiv)
        (auxIndexEquivFin n m k)).trans finSumFinEquiv)).trans
      (finSumFinEquiv.trans (finCongr (auxWidth_succ n m k).symm))

theorem rowIndex_card (r m k : ℕ) : Fintype.card (RowIndex r m k) = rowWidth r m k := by
  simpa using Fintype.card_congr (rowIndexEquivFin r m k)

theorem auxIndex_card (n m k : ℕ) : Fintype.card (AuxIndex n m k) = auxWidth n m k := by
  simpa using Fintype.card_congr (auxIndexEquivFin n m k)

variable {ρ' α' : Type*}

/-- Coordinate reindexing explicitly transports matrix-vector multiplication. -/
theorem reindex_mulVec [Fintype α] [Fintype α']
    (er : ρ ≃ ρ') (ea : α ≃ α') (N : Matrix ρ α ℝ) (b : α' → ℝ) :
    (Matrix.reindex er ea N).mulVec b =
      fun i => N.mulVec (fun j => b (ea j)) (er.symm i) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply]
  simpa using (Equiv.sum_comp ea (fun j => N (er.symm i) (ea.symm j) * b j)).symm

/-- Reindexing the rows and auxiliary coordinates preserves existential feasibility. -/
theorem reindex_feasible_iff [Fintype α] [Fintype α']
    (er : ρ ≃ ρ') (ea : α ≃ α')
    (K : Matrix ρ (Fin n) ℝ) (N : Matrix ρ α ℝ) (v : Fin n → ℝ) :
    (∃ b, (Matrix.reindex er (Equiv.refl _) K).mulVec v +
      (Matrix.reindex er ea N).mulVec b = 0) ↔
      ∃ a, K.mulVec v + N.mulVec a = 0 := by
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨fun j => b (ea j), ?_⟩
    ext i
    have hi := congrFun hb (er i)
    simpa only [Pi.add_apply, reindex_mulVec, Equiv.symm_apply_apply,
      Equiv.refl_apply, Pi.zero_apply] using hi
  · rintro ⟨a, ha⟩
    refine ⟨fun j => a (ea.symm j), ?_⟩
    ext i
    have hi := congrFun ha (er.symm i)
    simpa only [Pi.add_apply, reindex_mulVec, Equiv.symm_apply_apply,
      Equiv.refl_apply, Pi.zero_apply] using hi

/-- Horizontal concatenation commutes with simultaneous coordinate reindexing. -/
theorem fromCols_reindex (er : ρ ≃ ρ') (ea : α ≃ α')
    (K : Matrix ρ (Fin n) ℝ) (N : Matrix ρ α ℝ) :
    Matrix.fromCols (Matrix.reindex er ea N) (Matrix.reindex er (Equiv.refl _) K) =
      Matrix.reindex er (Equiv.sumCongr ea (Equiv.refl _)) (Matrix.fromCols N K) := by
  ext i j
  rcases j with j | j <;> rfl

/-- The rectangular Fin-indexed matrices with exactly the paper's a_{k+1},b_{k+1}. -/
def finitePair
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin m → Matrix (Fin n) (Fin r) ℝ) (k : ℕ) :
    Matrix (Fin (rowWidth r m k)) (Fin n) ℝ ×
      Matrix (Fin (rowWidth r m k)) (Fin (auxWidth n m k)) ℝ :=
    (Matrix.reindex (rowIndexEquivFin r m k) (Equiv.refl _) (matrixPair A B C D k).1,
      Matrix.reindex (rowIndexEquivFin r m k) (auxIndexEquivFin n m k) (matrixPair A B C D k).2)

/-- The finite-coordinate form of paper (eq:rank-identity). -/
theorem finitePair_feasible_iff
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin m → Matrix (Fin n) (Fin r) ℝ) (k : ℕ) (v : Fin n → ℝ) :
    (∃ a, (finitePair A B C D k).1.mulVec v + (finitePair A B C D k).2.mulVec a = 0) ↔
      v ∈ (AdjointCoefficients.fromMatrices A B C D).flag (k + 1) := by
  unfold finitePair
  rw [reindex_feasible_iff]
  exact matrixPair_feasible_iff A B C D k v

/-- The finite-coordinate form of paper (eq:rank-codimension). -/
theorem finitePair_rank_codimension
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin m → Matrix (Fin n) (Fin r) ℝ) (k : ℕ) :
    (Matrix.fromCols (finitePair A B C D k).2 (finitePair A B C D k).1).rank -
      (finitePair A B C D k).2.rank =
      n - finrank ℝ ((AdjointCoefficients.fromMatrices A B C D).flag (k + 1)) := by
  simp only [finitePair, fromCols_reindex, Matrix.rank_reindex]
  exact matrixPair_rank_codimension A B C D k

#print axioms finitePair_feasible_iff
#print axioms finitePair_rank_codimension

end Coordinates
end LinearStochastic
