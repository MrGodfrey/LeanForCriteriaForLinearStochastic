import LinearStochastic.RealQEProjectionCorrectness
import LinearStochastic.SemialgebraicCoordinates
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Existential real quantifier elimination for polynomial sign formulas

The symbolic coefficient projection has a proved ordered-sign-table invariant.
A finite three-way sign decomposition then constructs a quantifier-free formula.
This is an existence theorem over arbitrary real coefficients; the final finite
truth labels use classical logic, so no executable QE decision procedure is claimed.
-/
noncomputable section
namespace LinearStochastic.RealQEExistential
open SemialgebraicCoordinates RealQEFiniteCells RealQERecursiveProjection RealQEProjectionCorrectness
variable {σ : Type*}

/-- The actual finite polynomial atoms of the existing quantifier-free syntax. -/
def atoms : SignFormula σ → List (MvPolynomial σ ℝ)
  | .falsum => []
  | .zero p => [p]
  | .positive p => [p]
  | .neg φ => atoms φ
  | .conj φ ψ => atoms φ ++ atoms ψ
  | .disj φ ψ => atoms φ ++ atoms ψ

/-- Truth depends only on the signs of the actual polynomial atoms. -/
theorem holds_of_same_signs (φ : SignFormula σ) (v w : σ → ℝ)
    (h : ∀ p ∈ atoms φ, SameSign (MvPolynomial.eval v p) (MvPolynomial.eval w p)) :
    φ.Holds v ↔ φ.Holds w := by
  induction φ with
  | falsum => rfl
  | zero p => exact (h p (by simp [atoms])).1
  | positive p => exact (h p (by simp [atoms])).2
  | neg φ ih => exact not_congr (ih h)
  | conj φ ψ ih jh =>
    exact and_congr (ih (fun p hp => h p (List.mem_append_left _ hp)))
      (jh (fun p hp => h p (List.mem_append_right _ hp)))
  | disj φ ψ ih jh =>
    exact or_congr (ih (fun p hp => h p (List.mem_append_left _ hp)))
      (jh (fun p hp => h p (List.mem_append_right _ hp)))

/-- A subset whose membership is determined by finitely many polynomial signs
has a quantifier-free formula. The induction really builds the finite sign branches;
the base case only chooses the truth value of one completely determined branch. -/
theorem finite_sign_formula_on (cs : List (MvPolynomial σ ℝ)) (A S : (σ → ℝ) → Prop)
    (hdet : ∀ v w, A v → A w →
      (∀ c ∈ cs, SameSign (MvPolynomial.eval v c) (MvPolynomial.eval w c)) → (S v ↔ S w)) :
    ∃ φ : SignFormula σ, ∀ v, A v → (φ.Holds v ↔ S v) := by
  classical
  induction cs generalizing A with
  | nil =>
    by_cases hs : ∃ v, A v ∧ S v
    · obtain ⟨w,hw,hSw⟩ := hs
      refine ⟨.neg .falsum,?_⟩
      intro v hv
      have hSv : S v := (hdet w v hw hv (by simp)).mp hSw
      simp only [SignFormula.Holds,not_false_eq_true,true_iff]
      exact hSv
    · refine ⟨.falsum,?_⟩
      intro v hv
      constructor
      · exact False.elim
      · intro hSv
        exact hs ⟨v,hv,hSv⟩
  | cons p cs ih =>
    obtain ⟨φzero,hzero⟩ := ih (fun v => A v ∧ MvPolynomial.eval v p = 0) (by
      intro v w hv hw hcs
      apply hdet v w hv.1 hw.1
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · simp only [hv.2,hw.2]
        exact SameSign.refl 0
      · exact hcs c hc)
    obtain ⟨φpos,hpos⟩ := ih (fun v => A v ∧ 0 < MvPolynomial.eval v p) (by
      intro v w hv hw hcs
      apply hdet v w hv.1 hw.1
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨by simp [ne_of_gt hv.2,ne_of_gt hw.2],by simp [hv.2,hw.2]⟩
      · exact hcs c hc)
    obtain ⟨φneg,hneg⟩ := ih (fun v => A v ∧ MvPolynomial.eval v p < 0) (by
      intro v w hv hw hcs
      apply hdet v w hv.1 hw.1
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨by simp [ne_of_lt hv.2,ne_of_lt hw.2],by simp [not_lt_of_gt hv.2,not_lt_of_gt hw.2]⟩
      · exact hcs c hc)
    refine ⟨.disj (.conj (.zero p) φzero)
      (.disj (.conj (.positive p) φpos) (.conj (.positive (-p)) φneg)),?_⟩
    intro v hv
    simp only [SignFormula.Holds,MvPolynomial.eval_neg,neg_pos]
    constructor
    · rintro (⟨hz,hφ⟩ | ⟨hp,hφ⟩ | ⟨hn,hφ⟩)
      · exact (hzero v ⟨hv,hz⟩).mp hφ
      · exact (hpos v ⟨hv,hp⟩).mp hφ
      · exact (hneg v ⟨hv,hn⟩).mp hφ
    · intro hSv
      rcases lt_trichotomy (MvPolynomial.eval v p) 0 with hn | hz | hp
      · exact Or.inr (Or.inr ⟨hn,(hneg v ⟨hv,hn⟩).mpr hSv⟩)
      · exact Or.inl ⟨hz,(hzero v ⟨hv,hz⟩).mpr hSv⟩
      · exact Or.inr (Or.inl ⟨hp,(hpos v ⟨hv,hp⟩).mpr hSv⟩)

theorem finite_sign_determined_semialgebraic (cs : List (MvPolynomial σ ℝ))
    (S : Set (σ → ℝ))
    (hdet : ∀ v w, (∀ c ∈ cs, SameSign (MvPolynomial.eval v c) (MvPolynomial.eval w c)) →
      (v ∈ S ↔ w ∈ S)) : IsSemialgebraic S := by
  obtain ⟨φ,hφ⟩ := finite_sign_formula_on cs (fun _ => True) (fun v => v ∈ S)
    (fun v w _ _ hc => hdet v w hc)
  exact ⟨φ,fun v => hφ v trivial⟩

/-- none is the quantified variable; some i is the retained parameter coordinate. -/
def extend (v : σ → ℝ) (x : ℝ) : Option σ → ℝ := fun i => Option.elim i x v

/-- The library's actual polynomial equivalence preserves this precise variable order. -/
theorem eval_option_polynomial (p : MvPolynomial (Option σ) ℝ) (v : σ → ℝ) (x : ℝ) :
    (MvPolynomial.optionEquivLeft ℝ σ p).eval₂ (MvPolynomial.eval v) x =
      MvPolynomial.eval (extend v x) p := by
  change (MvPolynomial.optionEquivLeft ℝ σ p).eval₂ (MvPolynomial.eval v) x =
    MvPolynomial.eval (fun i : Option σ => Option.elim i x v) p
  simpa only [Polynomial.eval_map] using
    (MvPolynomial.optionEquivLeft_elim_eval (R := ℝ) (S₁ := σ) v x p).symm

/-- The finite coefficient list used to eliminate exactly one real variable. -/
def existentialCoefficients (φ : SignFormula (Option σ)) : List (MvPolynomial σ ℝ) :=
  projectionCoefficients ((atoms φ).map (MvPolynomial.optionEquivLeft ℝ σ))

/-- The proved projection invariant transfers a witness for every Boolean sign formula. -/
theorem existential_truth_same_signs (φ : SignFormula (Option σ)) (v w : σ → ℝ)
    (h : ∀ c ∈ existentialCoefficients φ,
      SameSign (MvPolynomial.eval v c) (MvPolynomial.eval w c)) :
    (∃ x, φ.Holds (extend v x)) ↔ ∃ y, φ.Holds (extend w y) := by
  have transfer (v w : σ → ℝ)
      (h : ∀ c ∈ existentialCoefficients φ,
        SameSign (MvPolynomial.eval v c) (MvPolynomial.eval w c))
      (x : ℝ) : ∃ y, φ.Holds (extend v x) ↔ φ.Holds (extend w y) := by
    obtain ⟨y,hy⟩ := projection_sign_witness
      ((atoms φ).map (MvPolynomial.optionEquivLeft ℝ σ)) (MvPolynomial.eval v) (MvPolynomial.eval w) h x
    refine ⟨y,holds_of_same_signs φ _ _ ?_⟩
    intro p hp
    have hs := hy (MvPolynomial.optionEquivLeft ℝ σ p) (List.mem_map.mpr ⟨p,hp,rfl⟩)
    simpa only [eval_option_polynomial] using hs
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨y,hy⟩ := transfer v w h x
    exact ⟨y,hy.mp hx⟩
  · rintro ⟨y,hy⟩
    obtain ⟨x,hx⟩ := transfer w v (fun c hc => (h c hc).symm) y
    exact ⟨x,hx.mp hy⟩

/-- Eliminate one existentially quantified real variable from the existing
polynomial sign syntax. No projection or QE hypothesis appears in the theorem. -/
theorem exists_formula (φ : SignFormula (Option σ)) :
    ∃ ψ : SignFormula σ, ∀ v, ψ.Holds v ↔ ∃ x : ℝ, φ.Holds (extend v x) := by
  exact finite_sign_determined_semialgebraic (existentialCoefficients φ)
    {v | ∃ x : ℝ, φ.Holds (extend v x)} (existential_truth_same_signs φ)

/-- Tarski–Seidenberg projection for a single real coordinate in standard
multivariate-polynomial semialgebraic sets. -/
theorem exists_option (S : Set (Option σ → ℝ)) (hS : IsSemialgebraic S) :
    IsSemialgebraic {v : σ → ℝ | ∃ x : ℝ, extend v x ∈ S} := by
  obtain ⟨φ,hφ⟩ := hS
  obtain ⟨ψ,hψ⟩ := exists_formula φ
  refine ⟨ψ,?_⟩
  intro v
  simpa only [hφ,Set.mem_ofPred_eq] using hψ v

#print axioms finite_sign_determined_semialgebraic
#print axioms existential_truth_same_signs
#print axioms exists_formula
#print axioms exists_option
end LinearStochastic.RealQEExistential
