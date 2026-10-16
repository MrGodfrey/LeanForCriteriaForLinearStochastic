import LinearStochastic.AlgebraSurjective
import LinearStochastic.AlgebraWordTransport

/-!
# Original matrix coefficients and the reduced word-rank obstruction

The generator order is E₁,...,Eₘ,F. Euclidean realization is used solely to
form adjoints and the canonical Gram inverse; all displayed word blocks are
literal matrices, and their rank is the usual Mathlib matrix rank.
-/
noncomputable section
namespace LinearStochastic.SurjectiveMatrices
open Module
open scoped BigOperators
variable {n r m : ℕ}

/-- The vertically stacked diffusion-control matrix of the paper. -/
def stack (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    Matrix (Fin m × Fin n) (Fin r) ℝ := fun p j => D p.1 p.2 j

theorem stack_mulVec (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (u : Fin r → ℝ) (i : Fin m) (j : Fin n) :
    (stack D).mulVec u (i,j) = (D i).mulVec u j := rfl

/-- Full row rank of the concrete stacked matrix is precisely surjectivity of joint diffusion. -/
theorem stack_full_rank_iff (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    (stack D).rank = m*n ↔
      Function.Surjective (InputStructure.jointDiffusion (fun i => (D i).toEuclideanLin)) := by
  have hr : (stack D).rank = m*n ↔ Function.Surjective (stack D).mulVecLin := by
    rw [← LinearMap.range_eq_top]
    constructor
    · intro h
      apply Submodule.eq_top_of_finrank_eq
      simpa only [Matrix.rank, Module.finrank_pi, Module.finrank_self, Fintype.card_prod,
        Fintype.card_fin, mul_one] using h
    · intro h
      change finrank ℝ (stack D).mulVecLin.range = m*n
      rw [h, finrank_top]
      simp
  rw [hr]
  constructor
  · intro hs y
    obtain ⟨u, hu⟩ := hs (fun p => y p.1 p.2)
    refine ⟨WithLp.toLp 2 u, ?_⟩
    ext i j
    exact congrFun hu (i,j)
  · intro hs y
    obtain ⟨u, hu⟩ := hs (WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => y (i,j))))
    refine ⟨u.ofLp, ?_⟩
    funext p
    exact congrArg (fun z => z p.1 p.2) hu

variable (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hD : (stack D).rank = m*n)

/-- H=B(I−JD), in the original standard orthonormal bases. -/
def reducedH : Matrix (Fin n) (Fin r) ℝ :=
  Matrix.toEuclideanLin.symm (SurjectiveReduction.forwardH B.toEuclideanLin
    (fun i => (D i).toEuclideanLin) ((stack_full_rank_iff D).mp hD))

/-- Exact ordered family E₁,...,Eₘ,F, in the original standard orthonormal basis. -/
def reducedGenerators : Fin (m+1) → Matrix (Fin n) (Fin n) ℝ := fun i =>
  Matrix.toEuclideanLin.symm (SurjectiveReduction.forwardGenerators A.toEuclideanLin
    B.toEuclideanLin (fun j => (C j).toEuclideanLin) (fun j => (D j).toEuclideanLin)
    ((stack_full_rank_iff D).mp hD) (finSuccEquivLast i))

theorem reducedGenerators_channel (i : Fin m) :
    reducedGenerators A B C D hD i.castSucc =
      Matrix.toEuclideanLin.symm (SurjectiveReduction.forwardE B.toEuclideanLin
        (fun j => (D j).toEuclideanLin) ((stack_full_rank_iff D).mp hD) i) := by
  simp [reducedGenerators, SurjectiveReduction.forwardGenerators]

theorem reducedGenerators_drift :
    reducedGenerators A B C D hD (Fin.last m) =
      Matrix.toEuclideanLin.symm (SurjectiveReduction.forwardF A.toEuclideanLin B.toEuclideanLin
        (fun j => (C j).toEuclideanLin) (fun j => (D j).toEuclideanLin)
        ((stack_full_rank_iff D).mp hD)) := by
  simp [reducedGenerators, SurjectiveReduction.forwardGenerators]

/-- The algebraic statement behind prop:exact-rank, for the actual coefficient matrices.
The controllability equivalence requires the stochastic classification theorem separately. -/
theorem flag_bot_iff_word_matrix_full_rank :
    (InputStructure.fromForward A.toEuclideanLin B.toEuclideanLin
      (fun j => (C j).toEuclideanLin) (fun j => (D j).toEuclideanLin)).flag n = ⊥ ↔
    (WordMatrices.cumulativeMatrix (reducedGenerators A B C D hD)
      (reducedH B D hD) (n-1)).rank = n := by
  have hc := SurjectiveReduction.canonical_flag_bot_iff A.toEuclideanLin B.toEuclideanLin
    (fun j => (C j).toEuclideanLin) (fun j => (D j).toEuclideanLin)
    ((stack_full_rank_iff D).mp hD)
  simp only [finrank_euclideanSpace_fin] at hc
  rw [hc, WordMatrices.cumulativeMatrix_full_rank_iff_euclidean]
  simp only [reducedGenerators, reducedH, LinearEquiv.apply_symm_apply]
  rw [Words.wordSpan_reindex finSuccEquivLast]

#print axioms flag_bot_iff_word_matrix_full_rank
end LinearStochastic.SurjectiveMatrices
