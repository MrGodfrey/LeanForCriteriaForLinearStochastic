import LinearStochastic.RealQEFiniteProjection
import LinearStochastic.LMIPolynomial

noncomputable section
namespace LinearStochastic.MatrixSemialgebraic
open scoped BigOperators
open MvPolynomial SemialgebraicCoordinates LMIPolynomial RealQEFiniteProjection
variable {σ ι : Type*} [Fintype ι]

/-- Positive semidefiniteness of a polynomial matrix is semialgebraic by actual
finite real quantifier elimination of its quadratic form. -/
theorem isSemialgebraic_posSemidef (M : Matrix ι ι (MvPolynomial σ ℝ)) :
    IsSemialgebraic {v | (M.map (MvPolynomial.eval v)).PosSemidef} := by
  let M' : Matrix ι ι (MvPolynomial (σ ⊕ ι) ℝ) := fun i j => MvPolynomial.rename Sum.inl (M i j)
  let q : MvPolynomial (σ ⊕ ι) ℝ := quadratic M' (fun i => MvPolynomial.X (Sum.inr i))
  have he (v : σ → ℝ) (u : ι → ℝ) :
      MvPolynomial.eval (Sum.elim v u) q = dotProduct u ((M.map (MvPolynomial.eval v)).mulVec u) := by
    simp [q,quadratic,M',Matrix.mulVec,dotProduct,Matrix.map_apply,MvPolynomial.eval_rename,
      Function.comp_def]
  have h := forall_finite {w | 0 ≤ MvPolynomial.eval w q} (isSemialgebraic_nonneg q)
  have hs := (isSemialgebraic_symmetric M).inter h
  convert hs using 1
  ext v
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec,Matrix.isHermitian_iff_isSymm,
    Set.mem_inter_iff,Set.mem_ofPred_eq,he,star_trivial]

variable {n r m : ℕ}

def normalizedEntries
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C₀ : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : MvPolynomial σ ℝ) (P : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (K : Matrix (Fin r) (Fin n) (MvPolynomial σ ℝ)) :=
  -entries A B C₀ D ρ P K - 1

theorem eval_normalizedEntries
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C₀ : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : MvPolynomial σ ℝ) (P : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (K : Matrix (Fin r) (Fin n) (MvPolynomial σ ℝ)) (v : σ → ℝ) :
    (normalizedEntries A B C₀ D ρ P K).map (MvPolynomial.eval v) =
      -LMIMatrixCoordinates.matrixLMI A B C₀ D (MvPolynomial.eval v ρ)
        (P.map (MvPolynomial.eval v)) (K.map (MvPolynomial.eval v)) - 1 := by
  rw [←eval_entries A B C₀ D ρ P K v]
  ext i j
  simp only [normalizedEntries,Matrix.map_apply,Matrix.sub_apply,Matrix.neg_apply,map_sub,map_neg,
    Matrix.one_apply]
  split_ifs <;> simp

/-- The exact normalized feasible matrix relation with arbitrary polynomial
coordinate inputs is semialgebraic, not a surrogate positivity predicate. -/
theorem isSemialgebraic_feasible
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C₀ : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : MvPolynomial σ ℝ) (P : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (K : Matrix (Fin r) (Fin n) (MvPolynomial σ ℝ)) :
    IsSemialgebraic {v | MatrixNormalization.Feasible A B C₀ D (MvPolynomial.eval v ρ)
      (P.map (MvPolynomial.eval v)) (K.map (MvPolynomial.eval v))} := by
  have h := (isSemialgebraic_symmetric P).inter
    (isSemialgebraic_posSemidef (normalizedEntries A B C₀ D ρ P K))
  simpa only [MatrixNormalization.Feasible,Set.ofPred_and,eval_normalizedEntries] using h

end LinearStochastic.MatrixSemialgebraic
