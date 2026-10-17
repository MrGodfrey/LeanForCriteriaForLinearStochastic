module

public import LinearStochastic.SemialgebraicTail
public import Mathlib.Algebra.MvPolynomial.Basic

@[expose] public section

/-!
# Standard multivariate-polynomial coordinates for semialgebraic graph growth

Variables 0 and 1 are respectively the parameter and function value. The
translation is an actual polynomial substitution with a proved evaluation identity.
-/
noncomputable section
namespace LinearStochastic.SemialgebraicCoordinates
open SemialgebraicTail

/-- Standard real multivariate polynomials in two coordinates, represented as nested
univariate polynomials. This is an explicit ring homomorphism. -/
def toBivariate : MvPolynomial (Fin 2) ℝ →+* Bivariate :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    (fun i => if i = 0 then Polynomial.C Polynomial.X else Polynomial.X)

/-- Evaluation respects the actual parameter/value order (t,s). -/
theorem evaluate_toBivariate (P : MvPolynomial (Fin 2) ℝ) (t s : ℝ) :
    evaluate (toBivariate P) t s = MvPolynomial.eval ![t,s] P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [toBivariate, evaluate, specialize]
  | add P Q hP hQ =>
    simpa [evaluate, specialize] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    fin_cases i <;> simp_all [toBivariate, evaluate, specialize]

/-- Finite Boolean combinations of zero and positive multivariate polynomial tests,
the ordinary definition of a real semialgebraic formula. -/
inductive SignFormula (σ : Type*) where
  | falsum : SignFormula σ
  | zero (p : MvPolynomial σ ℝ) : SignFormula σ
  | positive (p : MvPolynomial σ ℝ) : SignFormula σ
  | neg (φ : SignFormula σ) : SignFormula σ
  | conj (φ ψ : SignFormula σ) : SignFormula σ
  | disj (φ ψ : SignFormula σ) : SignFormula σ

def SignFormula.Holds {σ : Type*} : SignFormula σ → (σ → ℝ) → Prop
  | .falsum, _ => False
  | .zero p, v => MvPolynomial.eval v p = 0
  | .positive p, v => 0 < MvPolynomial.eval v p
  | .neg φ, v => ¬φ.Holds v
  | .conj φ ψ, v => φ.Holds v ∧ ψ.Holds v
  | .disj φ ψ, v => φ.Holds v ∨ ψ.Holds v

def SignFormula.toFormula : SignFormula (Fin 2) → Formula
  | .falsum => .falsum
  | .zero p => .zero (toBivariate p)
  | .positive p => .positive (toBivariate p)
  | .neg φ => .neg φ.toFormula
  | .conj φ ψ => .conj φ.toFormula ψ.toFormula
  | .disj φ ψ => .disj φ.toFormula ψ.toFormula

theorem SignFormula.toFormula_holds (φ : SignFormula (Fin 2)) (t s : ℝ) :
    φ.toFormula.Holds t s ↔ φ.Holds ![t,s] := by
  induction φ with
  | falsum => rfl
  | zero p => exact (congrArg (· = 0) (evaluate_toBivariate p t s)).to_iff
  | positive p => exact (congrArg (0 < ·) (evaluate_toBivariate p t s)).to_iff
  | neg φ ih => exact not_congr ih
  | conj φ ψ ih jh => exact and_congr ih jh
  | disj φ ψ ih jh => exact or_congr ih jh

/-- The standard sign-formula definition of a semialgebraic set. -/
def IsSemialgebraic {σ : Type*} (S : Set (σ → ℝ)) : Prop :=
  ∃ φ : SignFormula σ, ∀ v, φ.Holds v ↔ v ∈ S

/-- Standard coordinate graph on the closed ray [1,∞). -/
def rayGraph (f : ℝ → ℝ) : Set (Fin 2 → ℝ) :=
  {v | 1 ≤ v 0 ∧ v 1 = f (v 0)}

/-- A standard multivariate semialgebraic graph supplies the nested-polynomial graph
used in the analytic proof, with no projection theorem inserted. -/
theorem rayGraph_to_nested (f : ℝ → ℝ) (h : IsSemialgebraic (rayGraph f)) :
    SemialgebraicGraph f := by
  obtain ⟨φ,hφ⟩ := h
  refine ⟨φ.toFormula, ?_⟩
  intro t ht s
  rw [φ.toFormula_holds, hφ]
  simp [rayGraph, ht]

/-- The manuscript's complete semialgebraic growth lemma, now with the standard
MvPolynomial finite-sign definition of semialgebraicity. -/
theorem continuous_semialgebraic_growth (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 1)) (hg : IsSemialgebraic (rayGraph f)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, 1 ≤ p ∧ ∀ t, 1 ≤ t → |f t| ≤ C*t^p :=
  SemialgebraicTail.continuous_semialgebraic_growth f hf (rayGraph_to_nested f hg)

#print axioms evaluate_toBivariate
#print axioms continuous_semialgebraic_growth
end LinearStochastic.SemialgebraicCoordinates
