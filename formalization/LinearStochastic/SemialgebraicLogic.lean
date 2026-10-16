import LinearStochastic.SemialgebraicCoordinates
import Mathlib.Algebra.MvPolynomial.CommRing

noncomputable section
namespace LinearStochastic.SemialgebraicCoordinates
open MvPolynomial
variable {σ τ : Type*}

/-- Literal polynomial substitution in a finite sign formula. -/
def SignFormula.subst (p : σ → MvPolynomial τ ℝ) : SignFormula σ → SignFormula τ
  | .falsum => .falsum
  | .zero q => .zero (MvPolynomial.eval₂ (MvPolynomial.C) p q)
  | .positive q => .positive (MvPolynomial.eval₂ (MvPolynomial.C) p q)
  | .neg φ => .neg (φ.subst p)
  | .conj φ ψ => .conj (φ.subst p) (ψ.subst p)
  | .disj φ ψ => .disj (φ.subst p) (ψ.subst p)

theorem eval_subst (p : σ → MvPolynomial τ ℝ) (q : MvPolynomial σ ℝ) (v : τ → ℝ) :
    MvPolynomial.eval v (MvPolynomial.eval₂ C p q) =
      MvPolynomial.eval (fun i => MvPolynomial.eval v (p i)) q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add q r hq hr => simp [hq,hr]
  | mul_X q i hq => simp [hq]

theorem SignFormula.subst_holds (p : σ → MvPolynomial τ ℝ)
    (φ : SignFormula σ) (v : τ → ℝ) :
    (φ.subst p).Holds v ↔ φ.Holds (fun i => MvPolynomial.eval v (p i)) := by
  induction φ with
  | falsum => rfl
  | zero q => simp only [SignFormula.subst,SignFormula.Holds,eval_subst]
  | positive q => simp only [SignFormula.subst,SignFormula.Holds,eval_subst]
  | neg φ ih => exact not_congr ih
  | conj φ ψ ih jh => exact and_congr ih jh
  | disj φ ψ ih jh => exact or_congr ih jh

theorem IsSemialgebraic.polynomial_preimage {S : Set (σ → ℝ)} (h : IsSemialgebraic S)
    (p : σ → MvPolynomial τ ℝ) :
    IsSemialgebraic {v | (fun i => MvPolynomial.eval v (p i)) ∈ S} := by
  obtain ⟨φ,hφ⟩ := h
  exact ⟨φ.subst p,fun v => (φ.subst_holds p v).trans (hφ _)⟩

theorem IsSemialgebraic.rename_preimage {S : Set (σ → ℝ)} (h : IsSemialgebraic S)
    (f : σ → τ) : IsSemialgebraic {v | (v ∘ f) ∈ S} := by
  simpa only [MvPolynomial.eval_X,Function.comp_def] using h.polynomial_preimage (fun i => MvPolynomial.X (f i))

theorem isSemialgebraic_empty : IsSemialgebraic (∅ : Set (σ → ℝ)) :=
  ⟨.falsum,fun _ => Iff.rfl⟩

theorem isSemialgebraic_univ : IsSemialgebraic (Set.univ : Set (σ → ℝ)) :=
  ⟨.neg .falsum,fun _ => by simp [SignFormula.Holds]⟩

theorem IsSemialgebraic.compl {S : Set (σ → ℝ)} (h : IsSemialgebraic S) :
    IsSemialgebraic Sᶜ := by
  obtain ⟨φ,hφ⟩ := h
  exact ⟨.neg φ,fun v => not_congr (hφ v)⟩

theorem IsSemialgebraic.inter {S T : Set (σ → ℝ)}
    (h : IsSemialgebraic S) (k : IsSemialgebraic T) : IsSemialgebraic (S ∩ T) := by
  obtain ⟨φ,hφ⟩ := h
  obtain ⟨ψ,hψ⟩ := k
  exact ⟨.conj φ ψ,fun v => and_congr (hφ v) (hψ v)⟩

theorem IsSemialgebraic.union {S T : Set (σ → ℝ)}
    (h : IsSemialgebraic S) (k : IsSemialgebraic T) : IsSemialgebraic (S ∪ T) := by
  obtain ⟨φ,hφ⟩ := h
  obtain ⟨ψ,hψ⟩ := k
  exact ⟨.disj φ ψ,fun v => or_congr (hφ v) (hψ v)⟩

theorem isSemialgebraic_zero (p : MvPolynomial σ ℝ) :
    IsSemialgebraic {v | MvPolynomial.eval v p = 0} := ⟨.zero p,fun _ => Iff.rfl⟩

theorem isSemialgebraic_positive (p : MvPolynomial σ ℝ) :
    IsSemialgebraic {v | 0 < MvPolynomial.eval v p} := ⟨.positive p,fun _ => Iff.rfl⟩

theorem isSemialgebraic_nonneg (p : MvPolynomial σ ℝ) :
    IsSemialgebraic {v | 0 ≤ MvPolynomial.eval v p} := by
  simpa only [Set.compl_ofPred,not_lt,map_neg,neg_nonpos] using
    (isSemialgebraic_positive (-p)).compl

theorem isSemialgebraic_eq (p q : MvPolynomial σ ℝ) :
    IsSemialgebraic {v | MvPolynomial.eval v p = MvPolynomial.eval v q} := by
  simpa only [map_sub,sub_eq_zero] using isSemialgebraic_zero (p-q)

theorem isSemialgebraic_le (p q : MvPolynomial σ ℝ) :
    IsSemialgebraic {v | MvPolynomial.eval v p ≤ MvPolynomial.eval v q} := by
  simpa only [map_sub,sub_nonneg] using isSemialgebraic_nonneg (q-p)

theorem isSemialgebraic_lt (p q : MvPolynomial σ ℝ) :
    IsSemialgebraic {v | MvPolynomial.eval v p < MvPolynomial.eval v q} := by
  simpa only [map_sub,sub_pos] using isSemialgebraic_positive (q-p)

theorem isSemialgebraic_finset_all {ι : Type*} (s : Finset ι)
    (S : ι → Set (σ → ℝ)) (h : ∀ i ∈ s, IsSemialgebraic (S i)) :
    IsSemialgebraic {v | ∀ i ∈ s, v ∈ S i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (isSemialgebraic_univ (σ := σ))
  | @insert i s hi ih =>
    have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.mem_insert,forall_eq_or_imp,Set.ofPred_and,Set.ofPred_mem_eq] using
      (h i (Finset.mem_insert_self i s)).inter hs

theorem isSemialgebraic_fintype_all {ι : Type*} [Fintype ι]
    (S : ι → Set (σ → ℝ)) (h : ∀ i, IsSemialgebraic (S i)) :
    IsSemialgebraic {v | ∀ i, v ∈ S i} := by
  simpa only [Finset.mem_univ,forall_const] using
    isSemialgebraic_finset_all Finset.univ S (fun i _ => h i)

end LinearStochastic.SemialgebraicCoordinates
