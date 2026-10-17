module

public import LinearStochastic.SemialgebraicLogic
public import LinearStochastic.MatrixMinimum

@[expose] public section

noncomputable section
namespace LinearStochastic.LMIPolynomial
open scoped BigOperators Matrix.Norms.Frobenius
open MvPolynomial LMIMatrixCoordinates SemialgebraicCoordinates
variable {σ : Type*} {n r m : ℕ}

/-- Every entry of the literal block LMI is a polynomial in the rate and the
entries of P and K. Constants are the original coefficient matrices. -/
def entries
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C₀ : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : MvPolynomial σ ℝ) (P : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (K : Matrix (Fin r) (Fin n) (MvPolynomial σ ℝ)) :
    Matrix (Option (Fin m) × Fin n) (Option (Fin m) × Fin n) (MvPolynomial σ ℝ) :=
  fun a b => match a.1,b.1 with
  | none,none => (∑ k, C (A a.2 k)*P k b.2) + (∑ k, P a.2 k*C (A b.2 k)) +
      (∑ k, C (B a.2 k)*K k b.2) + (∑ k, K k a.2*C (B b.2 k)) + ρ*P a.2 b.2
  | some i,none => (∑ k, C (C₀ i a.2 k)*P k b.2) + (∑ k, C (D i a.2 k)*K k b.2)
  | none,some i => (∑ k, C (C₀ i b.2 k)*P k a.2) + (∑ k, C (D i b.2 k)*K k a.2)
  | some i,some j => if i=j then -P a.2 b.2 else 0

theorem eval_entries
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C₀ : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : MvPolynomial σ ℝ) (P : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (K : Matrix (Fin r) (Fin n) (MvPolynomial σ ℝ)) (v : σ → ℝ) :
    (entries A B C₀ D ρ P K).map (MvPolynomial.eval v) =
      matrixLMI A B C₀ D (MvPolynomial.eval v ρ) (P.map (MvPolynomial.eval v))
        (K.map (MvPolynomial.eval v)) := by
  ext ⟨a,i⟩ ⟨b,j⟩
  cases a <;> cases b
  all_goals simp only [Matrix.map_apply,entries,matrixLMI_state_state,
    matrixLMI_noise_state,matrixLMI_state_noise,matrixLMI_noise_noise]
  all_goals (try split_ifs) <;> simp [Matrix.add_apply,Matrix.mul_apply,Matrix.smul_apply,
    Matrix.transpose_apply]

/-- Squared Frobenius norm equals the literal finite sum of entry squares. -/
theorem frobenius_sq {ι κ : Type*} [Fintype ι] [Fintype κ] (P : Matrix ι κ ℝ) :
    ‖P‖^2 = ∑ i, ∑ j, P i j ^ 2 := by
  rw [Matrix.frobenius_norm_def,←Real.sqrt_eq_rpow]
  simp only [Real.rpow_two,Real.norm_eq_abs,sq_abs]
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))

def objective (P : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (K : Matrix (Fin r) (Fin n) (MvPolynomial σ ℝ)) : MvPolynomial σ ℝ :=
  (∑ i, ∑ j, P i j ^ 2) + (∑ i, ∑ j, K i j ^ 2)

theorem eval_objective (P : Matrix (Fin n) (Fin n) (MvPolynomial σ ℝ))
    (K : Matrix (Fin r) (Fin n) (MvPolynomial σ ℝ)) (v : σ → ℝ) :
    MvPolynomial.eval v (objective P K) =
      QuadraticMinimum.matrixObjective (P.map (MvPolynomial.eval v),K.map (MvPolynomial.eval v)) := by
  simp only [objective,QuadraticMinimum.matrixObjective,QuadraticMinimum.objective,
    frobenius_sq,Matrix.map_apply,map_add,map_sum,map_pow]

/-- Polynomial quadratic form; no definiteness predicate is hidden in the syntax. -/
def quadratic {ι : Type*} [Fintype ι] (M : Matrix ι ι (MvPolynomial σ ℝ))
    (x : ι → MvPolynomial σ ℝ) : MvPolynomial σ ℝ :=
  ∑ i, x i * ∑ j, M i j*x j

theorem eval_quadratic {ι : Type*} [Fintype ι]
    (M : Matrix ι ι (MvPolynomial σ ℝ)) (x : ι → MvPolynomial σ ℝ) (v : σ → ℝ) :
    MvPolynomial.eval v (quadratic M x) =
      dotProduct (fun i => MvPolynomial.eval v (x i))
        ((M.map (MvPolynomial.eval v)).mulVec (fun i => MvPolynomial.eval v (x i))) := by
  simp only [quadratic,dotProduct,Matrix.mulVec,Matrix.map_apply,map_sum,map_mul]

/-- Symmetry of a polynomial matrix is a finite conjunction of polynomial equations. -/
theorem isSemialgebraic_symmetric {ι : Type*} [Fintype ι]
    (P : Matrix ι ι (MvPolynomial σ ℝ)) :
    IsSemialgebraic {v | (P.map (MvPolynomial.eval v)).IsSymm} := by
  have h := isSemialgebraic_fintype_all (fun i : ι => {v | ∀ j : ι,
      MvPolynomial.eval v (P j i) = MvPolynomial.eval v (P i j)})
    (fun i => isSemialgebraic_fintype_all (fun j : ι => {v |
      MvPolynomial.eval v (P j i) = MvPolynomial.eval v (P i j)})
      (fun j => isSemialgebraic_eq _ _))
  convert h using 1
  ext v
  change (P.map (MvPolynomial.eval v)).transpose = P.map (MvPolynomial.eval v) ↔ _
  constructor
  · intro h i j
    exact congrFun (congrFun h i) j
  · intro h
    ext i j
    exact h i j

end LinearStochastic.LMIPolynomial
