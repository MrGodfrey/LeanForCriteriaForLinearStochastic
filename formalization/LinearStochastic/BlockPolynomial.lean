module

public import LinearStochastic.AlgebraCoordinates
public import Mathlib.Algebra.MvPolynomial.Eval

@[expose] public section

/-! Every literal recursively constructed matrix entry is a polynomial in
exactly the original finite coefficient entries. Evaluation yields the actual
paper matrices, including the final ordered Fin-indexed flattening. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BlockPolynomial
open scoped BigOperators
open MvPolynomial Coordinates
variable {n r m : ℕ} {σ : Type*}

def pair (A : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (B : Matrix (Fin n) (Fin r) (MvPolynomial σ ℝ))
    (C : Fin m → Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (D : Fin m → Matrix (Fin n) (Fin r) (MvPolynomial σ ℝ)) :
    (k : ℕ) → Matrix (RowIndex r m k) (Fin n) (MvPolynomial σ ℝ) ×
      Matrix (RowIndex r m k) (AuxIndex n m k) (MvPolynomial σ ℝ)
  | 0 => (B.transpose, fun i j => D j.1 j.2 i)
  | k+1 =>
    let p := pair A B C D k
    (Matrix.fromRows B.transpose (Matrix.fromRows 0 (p.1*A.transpose)),
      Matrix.fromRows
        (Matrix.fromCols (fun i j => D j.1 j.2 i) (Matrix.fromCols 0 0))
        (Matrix.fromRows
          (Matrix.fromCols ((1 : Matrix (Fin m) (Fin m) (MvPolynomial σ ℝ)).kronecker p.1)
            (Matrix.fromCols ((1 : Matrix (Fin m) (Fin m) (MvPolynomial σ ℝ)).kronecker p.2) 0))
          (Matrix.fromCols (p.1*(show Matrix (Fin n) (Fin m × Fin n) (MvPolynomial σ ℝ) from fun i j => C j.1 j.2 i)) (Matrix.fromCols 0 p.2))))

theorem eval_pair (A : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (B : Matrix (Fin n) (Fin r) (MvPolynomial σ ℝ))
    (C : Fin m → Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (D : Fin m → Matrix (Fin n) (Fin r) (MvPolynomial σ ℝ)) (v : σ → ℝ) (k : ℕ) :
    ((pair A B C D k).1.map (eval v),(pair A B C D k).2.map (eval v)) =
      matrixPair (A.map (eval v)) (B.map (eval v))
        (fun i => (C i).map (eval v)) (fun i => (D i).map (eval v)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hK := congrArg Prod.fst ih
    have hN := congrArg Prod.snd ih
    apply Prod.ext
    · ext i j
      rcases i with i | (⟨c,i⟩ | i)
      · rfl
      · simp [pair,matrixPair,nextK]
      · simp only [pair,matrixPair,nextK,Matrix.fromRows_apply_inr,Matrix.map_apply,
          Matrix.mul_apply,map_sum,map_mul,Matrix.transpose_apply]
        exact Finset.sum_congr rfl (fun a _ =>
          congrArg (fun z : ℝ => z * eval v (A j a)) (congrFun (congrFun hK i) a))
    · ext i j
      rcases i with i | (⟨c,i⟩ | i) <;>
        rcases j with ⟨d,j⟩ | (⟨d,j⟩ | j) <;>
        simp [pair,matrixPair,nextN,joint,Matrix.kroneckerMap,Matrix.one_apply,
          Matrix.mul_apply,Matrix.map_apply,map_sum,map_mul,←hK,←hN]
      all_goals split_ifs <;> simp_all

def CoeffIndex (n r m : ℕ) :=
  ((Fin n × Fin n) ⊕ (Fin n × Fin r)) ⊕
    (Fin m × ((Fin n × Fin n) ⊕ (Fin n × Fin r)))

instance : Fintype (CoeffIndex n r m) := inferInstanceAs (Fintype
  (((Fin n × Fin n) ⊕ (Fin n × Fin r)) ⊕
    (Fin m × ((Fin n × Fin n) ⊕ (Fin n × Fin r)))))

def values (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    CoeffIndex n r m → ℝ
  | .inl (.inl (i,j)) => A i j
  | .inl (.inr (i,j)) => B i j
  | .inr (a,.inl (i,j)) => C a i j
  | .inr (a,.inr (i,j)) => D a i j

def universal (n r m k : ℕ) := pair
  (fun i j => X (.inl (.inl (i,j)) : CoeffIndex n r m))
  (fun i j => X (.inl (.inr (i,j)) : CoeffIndex n r m))
  (fun a i j => X (.inr (a,.inl (i,j)) : CoeffIndex n r m))
  (fun a i j => X (.inr (a,.inr (i,j)) : CoeffIndex n r m)) k

/-- A single polynomial matrix pair, chosen before all real coefficients,
evaluates to exactly the actual recursive pair. No coefficient inverse occurs. -/
theorem universal_eval (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) (k : ℕ) :
    ((universal n r m k).1.map (eval (values A B C D)),
      (universal n r m k).2.map (eval (values A B C D))) = matrixPair A B C D k := by
  have hh := eval_pair (fun i j => X (.inl (.inl (i,j)) : CoeffIndex n r m))
      (fun i j => X (.inl (.inr (i,j)) : CoeffIndex n r m))
      (fun a i j => X (.inr (a,.inl (i,j)) : CoeffIndex n r m))
      (fun a i j => X (.inr (a,.inr (i,j)) : CoeffIndex n r m)) (values A B C D) k
  apply Eq.trans hh
  congr 1 <;> ext <;> simp [Matrix.map_apply,MvPolynomial.eval_X,values]

/-- Exact finite block entries have fixed coefficient polynomials, even at
rank deficient or zero coefficients. -/
theorem finite_entries_polynomial (k : ℕ) :
    (∀ i j, ∃ p : MvPolynomial (CoeffIndex n r m) ℝ, ∀ A B C D,
      eval (values A B C D) p = (finitePair A B C D k).1 i j) ∧
    (∀ i j, ∃ p : MvPolynomial (CoeffIndex n r m) ℝ, ∀ A B C D,
      eval (values A B C D) p = (finitePair A B C D k).2 i j) := by
  constructor
  · intro i j
    refine ⟨(universal n r m k).1 ((rowIndexEquivFin r m k).symm i) j,?_⟩
    intro A B C D
    exact congrFun (congrFun (congrArg Prod.fst (universal_eval A B C D k)) _) _
  · intro i j
    refine ⟨(universal n r m k).2 ((rowIndexEquivFin r m k).symm i)
      ((auxIndexEquivFin n m k).symm j),?_⟩
    intro A B C D
    exact congrFun (congrFun (congrArg Prod.snd (universal_eval A B C D k)) _) _

end LinearStochastic.BlockPolynomial
