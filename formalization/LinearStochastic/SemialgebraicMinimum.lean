import LinearStochastic.MatrixSemialgebraic
import LinearStochastic.MinimumGraph

noncomputable section
namespace LinearStochastic.SemialgebraicMinimum
open scoped Matrix.Norms.Frobenius
open MvPolynomial MatrixNormalization QuadraticMinimum SemialgebraicCoordinates
open RealQEFiniteProjection MatrixSemialgebraic
variable {n r m : ℕ}

abbrev PairIndex (n r : ℕ) := (Fin n × Fin n) ⊕ (Fin r × Fin n)

def readP (u : PairIndex n r → ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j => u (.inl (i,j))
def readK (u : PairIndex n r → ℝ) : Matrix (Fin r) (Fin n) ℝ := fun i j => u (.inr (i,j))
def encode (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ) : PairIndex n r → ℝ :=
  Sum.elim (fun ij => P ij.1 ij.2) (fun ij => K ij.1 ij.2)

theorem exists_pair_iff (R : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin r) (Fin n) ℝ → Prop) :
    (∃ u, R (readP u) (readK u)) ↔ ∃ P K, R P K := by
  constructor
  · rintro ⟨u,hu⟩
    exact ⟨readP u,readK u,hu⟩
  · rintro ⟨P,K,h⟩
    exact ⟨encode P K,h⟩

def pVariables : Matrix (Fin n) (Fin n) (MvPolynomial (Fin 2 ⊕ PairIndex n r) ℝ) :=
  fun i j => X (.inr (.inl (i,j)))
def kVariables : Matrix (Fin r) (Fin n) (MvPolynomial (Fin 2 ⊕ PairIndex n r) ℝ) :=
  fun i j => X (.inr (.inr (i,j)))

theorem eval_pVariables (v : Fin 2 → ℝ) (u : PairIndex n r → ℝ) :
    (pVariables (n := n) (r := r)).map (MvPolynomial.eval (Sum.elim v u)) = readP u := by
  ext i j
  simp [pVariables,readP]

theorem eval_kVariables (v : Fin 2 → ℝ) (u : PairIndex n r → ℝ) :
    (kVariables (n := n) (r := r)).map (MvPolynomial.eval (Sum.elim v u)) = readK u := by
  ext i j
  simp [kVariables,readK]

variable (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C₀ : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)

theorem isSemialgebraic_attainable_value : IsSemialgebraic {v : Fin 2 → ℝ |
    ∃ P K, Feasible A B C₀ D (v 0) P K ∧ matrixObjective (P,K) = v 1} := by
  have hf := isSemialgebraic_feasible A B C₀ D (X (.inl (0 : Fin 2))) pVariables kVariables
  have he := isSemialgebraic_eq (LMIPolynomial.objective (n := n) (r := r) pVariables kVariables) (X (.inl (1 : Fin 2)))
  have h := exists_finite _ (hf.inter he)
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,MvPolynomial.eval_X,Sum.elim_inl,
    eval_pVariables,eval_kVariables,LMIPolynomial.eval_objective] at h
  convert h using 1
  ext v
  exact (exists_pair_iff (fun P K => Feasible A B C₀ D (v 0) P K ∧ matrixObjective (P,K) = v 1)).symm

theorem isSemialgebraic_smaller_value : IsSemialgebraic {v : Fin 2 → ℝ |
    ∃ P K, Feasible A B C₀ D (v 0) P K ∧ matrixObjective (P,K) < v 1} := by
  have hf := isSemialgebraic_feasible A B C₀ D (X (.inl (0 : Fin 2))) pVariables kVariables
  have he := isSemialgebraic_lt (LMIPolynomial.objective (n := n) (r := r) pVariables kVariables) (X (.inl (1 : Fin 2)))
  have h := exists_finite _ (hf.inter he)
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,MvPolynomial.eval_X,Sum.elim_inl,
    eval_pVariables,eval_kVariables,LMIPolynomial.eval_objective] at h
  convert h using 1
  ext v
  exact (exists_pair_iff (fun P K => Feasible A B C₀ D (v 0) P K ∧ matrixObjective (P,K) < v 1)).symm

/-- The minimum graph is semialgebraic for the literal manuscript matrices and
Frobenius objective, using the fully proved real quantifier-elimination theorem. -/
theorem isSemialgebraic_minimum_graph
    (hfeas : ∀ ρ : Set.Ici (1 : ℝ), ∃ P K, Feasible A B C₀ D ρ P K) :
    IsSemialgebraic (rayGraph (MatrixValue.valueReal A B C₀ D hfeas)) := by
  have hr : IsSemialgebraic {v : Fin 2 → ℝ | 1 ≤ v 0} := by
    simpa only [map_one,MvPolynomial.eval_X] using
      isSemialgebraic_le (1 : MvPolynomial (Fin 2) ℝ) (X 0)
  have h := hr.inter ((isSemialgebraic_attainable_value A B C₀ D).inter
    (isSemialgebraic_smaller_value A B C₀ D).compl)
  convert h using 1
  ext v
  rw [MatrixValue.rayGraph_iff]
  simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_compl_iff]
  constructor
  · rintro ⟨hρ,P,K,hf,he,hn⟩
    exact ⟨hρ,⟨P,K,hf,he⟩,hn⟩
  · rintro ⟨hρ,⟨P,K,hf,he⟩,hn⟩
    exact ⟨hρ,P,K,hf,he,hn⟩

end LinearStochastic.SemialgebraicMinimum
