module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-!
# Polynomial tail bounds for quantifier-free real sign formulas

This module starts with actual finite Boolean formulas in bivariate polynomials.
It does not assume or assert real quantifier elimination. Projection of the LMI
feasibility formula into this syntax is a separate, outstanding theorem.
-/
noncomputable section
namespace LinearStochastic.SemialgebraicTail
open Polynomial Filter Asymptotics
open scoped BigOperators Topology

/-- A concrete eventual polynomial upper bound, including a positive integer exponent. -/
def PolynomialBound (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, 1 ≤ p ∧ ∀ᶠ t in atTop, |f t| ≤ C * t^p

/-- Every quotient of real polynomials with a nonzero denominator has such a bound.
The denominator's finitely many roots are discarded by the eventual quantifier. -/
theorem polynomial_ratio_bound (P Q : ℝ[X]) (hQ : Q ≠ 0) :
    PolynomialBound (fun t => P.eval t / Q.eval t) := by
  have hd : P.degree ≤ (Q * X^P.natDegree).degree := by
    rw [degree_mul_X_pow]
    exact P.degree_le_natDegree.trans (le_add_of_nonneg_left (zero_le_degree_iff.mpr hQ))
  obtain ⟨C, hC, hc⟩ := (isBigO_atTop_of_degree_le P (Q * X^P.natDegree) hd).exists_pos
  refine ⟨max C 1, le_max_right _ _, P.natDegree+1, by omega, ?_⟩
  filter_upwards [hc.bound, Q.eventually_atTop_not_isRoot hQ, eventually_ge_atTop (1 : ℝ)]
    with t ht hqt ht1
  have hq : Q.eval t ≠ 0 := hqt
  have ht0 : 0 ≤ t := le_trans zero_le_one ht1
  have hr : |P.eval t / Q.eval t| ≤ C * t^P.natDegree := by
    rw [abs_div, div_le_iff₀ (abs_pos.mpr hq)]
    simpa only [eval_mul, eval_pow, eval_X, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_nonneg ht0, mul_assoc, mul_comm, mul_left_comm] using ht
  exact hr.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ ht1 (Nat.le_succ _))
    (pow_nonneg ht0 _) (le_trans hC.le (le_max_left _ _)))

theorem PolynomialBound.zero : PolynomialBound (fun _ => 0) :=
  ⟨1, le_rfl, 1, le_rfl, by filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht; simpa using (le_trans zero_le_one ht)⟩

theorem PolynomialBound.abs {f : ℝ → ℝ} (h : PolynomialBound f) :
    PolynomialBound (fun t => |f t|) := by
  simpa only [PolynomialBound, abs_abs] using h

theorem PolynomialBound.add {f g : ℝ → ℝ} (hf : PolynomialBound f) (hg : PolynomialBound g) :
    PolynomialBound (fun t => f t + g t) := by
  obtain ⟨C, hC, p, hp, hb⟩ := hf
  obtain ⟨D, hD, q, hq, hd⟩ := hg
  refine ⟨C+D, by linarith, max p q, hp.trans (le_max_left _ _), ?_⟩
  filter_upwards [hb, hd, eventually_ge_atTop (1 : ℝ)] with t hf hg ht
  calc
    |f t + g t| ≤ |f t| + |g t| := abs_add_le _ _
    _ ≤ C*t^p + D*t^q := add_le_add hf hg
    _ ≤ C*t^(max p q) + D*t^(max p q) := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = (C+D)*t^(max p q) := by ring

theorem PolynomialBound.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (h : ∀ i ∈ s, PolynomialBound (f i)) : PolynomialBound (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PolynomialBound.zero
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- A convenient form of Cauchy's proved root bound, using a coefficient sum. -/
theorem root_abs_lt_ratio_sum (P : ℝ[X]) (hP : P ≠ 0) (s : ℝ) (hs : P.eval s = 0) :
    |s| < 1 + ∑ j ∈ Finset.range P.natDegree, |P.coeff j / P.leadingCoeff| := by
  have hb := (show P.IsRoot s from hs).norm_lt_cauchyBound hP
  have hsup : (Finset.range P.natDegree).sup (fun j => ‖P.coeff j‖₊) ≤
      ∑ j ∈ Finset.range P.natDegree, ‖P.coeff j‖₊ := by
    apply Finset.sup_le
    intro j hj
    exact Finset.single_le_sum (fun k _ => (show (0 : NNReal) ≤ ‖P.coeff k‖₊ from zero_le)) hj
  have hdiv := div_le_div_of_nonneg_right hsup
    (show (0 : NNReal) ≤ ‖P.leadingCoeff‖₊ from zero_le)
  unfold Polynomial.cauchyBound at hb
  have hh := lt_of_lt_of_le hb (add_le_add hdiv (le_refl (1 : NNReal)))
  change ‖s‖₊ < _ at hh
  have hh' := (NNReal.coe_lt_coe).mpr hh
  simpa only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_sum, NNReal.coe_one,
    coe_nnnorm, Real.norm_eq_abs, Finset.sum_div, abs_div, add_comm] using hh'

/-- A bivariate polynomial: the outer variable is the proposed size bound,
and the inner variable is the decay-rate parameter. -/
abbrev Bivariate := Polynomial (Polynomial ℝ)

def specialize (q : Bivariate) (t : ℝ) : ℝ[X] := q.map (Polynomial.evalRingHom t)
def evaluate (q : Bivariate) (t s : ℝ) : ℝ := (specialize q t).eval s

/-- Beyond a polynomial curve in the parameter, a nonzero bivariate polynomial has
no roots in the second variable. Exceptional parameter values disappear eventually. -/
theorem bivariate_eventually_no_roots (q : Bivariate) (hq : q ≠ 0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, 1 ≤ p ∧
      ∀ᶠ t in atTop, ∀ s, C*t^p ≤ s → evaluate q t s ≠ 0 := by
  have hl : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq
  have hb := PolynomialBound.sum (Finset.range q.natDegree)
    (fun j t => |(q.coeff j).eval t / q.leadingCoeff.eval t|)
    (fun j _ => (polynomial_ratio_bound (q.coeff j) q.leadingCoeff hl).abs)
  obtain ⟨C, hC, p, hp, hb⟩ := hb
  refine ⟨C+2, by linarith, p, hp, ?_⟩
  filter_upwards [hb, q.leadingCoeff.eventually_atTop_not_isRoot hl,
    eventually_ge_atTop (1 : ℝ)] with t ht hlt ht1
  have hlv : q.leadingCoeff.eval t ≠ 0 := hlt
  have hd : (specialize q t).natDegree = q.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero _ hlv
  have hlc : (specialize q t).leadingCoeff = q.leadingCoeff.eval t :=
    leadingCoeff_map_of_leadingCoeff_ne_zero _ hlv
  have hspec : specialize q t ≠ 0 := leadingCoeff_ne_zero.mp (hlc ▸ hlv)
  have hsum : (∑ j ∈ Finset.range q.natDegree,
      |(q.coeff j).eval t / q.leadingCoeff.eval t|) ≤ C*t^p := by
    rwa [abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))] at ht
  intro s hs hroot
  have hh := root_abs_lt_ratio_sum (specialize q t) hspec s hroot
  rw [hd, hlc] at hh
  simp only [specialize, coeff_map, coe_evalRingHom] at hh
  have hpow : 1 ≤ t^p := one_le_pow₀ ht1
  have hs0 : 0 ≤ s := (by positivity : 0 ≤ (C+2)*t^p).trans hs
  rw [abs_of_nonneg hs0] at hh
  nlinarith

/-- A continuous real function with no zeros on a ray has a fixed strict sign there. -/
theorem positive_iff_on_ray (f : ℝ → ℝ) (hf : Continuous f) (H : ℝ)
    (hne : ∀ x, H ≤ x → f x ≠ 0) (s u : ℝ) (hs : H ≤ s) (hu : H ≤ u) :
    0 < f s ↔ 0 < f u := by
  have step : ∀ a b, H ≤ a → H ≤ b → 0 < f a → 0 < f b := by
    intro a b ha hb hfa
    by_contra hfb
    have hfb' : f b ≤ 0 := le_of_not_gt hfb
    obtain ⟨x, hx, hfx⟩ := isPreconnected_Ici.intermediate_value hb ha hf.continuousOn
      (show 0 ∈ Set.Icc (f b) (f a) from ⟨hfb', hfa.le⟩)
    exact hne x hx hfx
  exact ⟨step s u hs hu, step u s hu hs⟩

/-- A finite Boolean formula in real bivariate polynomial sign tests. -/
inductive Formula where
  | falsum : Formula
  | zero (q : Bivariate) : Formula
  | positive (q : Bivariate) : Formula
  | neg (φ : Formula) : Formula
  | conj (φ ψ : Formula) : Formula
  | disj (φ ψ : Formula) : Formula

def Formula.Holds : Formula → ℝ → ℝ → Prop
  | .falsum, _, _ => False
  | .zero q, t, s => evaluate q t s = 0
  | .positive q, t, s => 0 < evaluate q t s
  | .neg φ, t, s => ¬φ.Holds t s
  | .conj φ ψ, t, s => φ.Holds t s ∧ ψ.Holds t s
  | .disj φ ψ, t, s => φ.Holds t s ∨ ψ.Holds t s

/-- Truth is constant in the second variable beyond a polynomial curve. -/
def TailStable (S : ℝ → ℝ → Prop) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, 1 ≤ p ∧ ∀ᶠ t in atTop,
    ∀ s u, C*t^p ≤ s → C*t^p ≤ u → (S t s ↔ S t u)

theorem TailStable.constant (b : Prop) : TailStable (fun _ _ => b) :=
  ⟨1, le_rfl, 1, le_rfl, Filter.Eventually.of_forall (fun _ _ _ _ _ => Iff.rfl)⟩

theorem TailStable.neg {S : ℝ → ℝ → Prop} (h : TailStable S) :
    TailStable (fun t s => ¬S t s) := by
  obtain ⟨C,hC,p,hp,ht⟩ := h
  exact ⟨C,hC,p,hp,ht.mono (fun t h s u hs hu => not_congr (h s u hs hu))⟩

/-- Two independently proved polynomial tails have a common polynomial tail. -/
theorem TailStable.combine {S T : ℝ → ℝ → Prop}
    (hS : TailStable S) (hT : TailStable T) (op : Prop → Prop → Prop)
    (hop : ∀ a b c d : Prop, (a ↔ c) → (b ↔ d) → (op a b ↔ op c d)) :
    TailStable (fun t s => op (S t s) (T t s)) := by
  obtain ⟨C,hC,p,hp,hS⟩ := hS
  obtain ⟨D,hD,q,hq,hT⟩ := hT
  refine ⟨C+D, by linarith, max p q, hp.trans (le_max_left _ _), ?_⟩
  filter_upwards [hS,hT,eventually_ge_atTop (1 : ℝ)] with t hs ht ht1
  have hc : C*t^p ≤ (C+D)*t^(max p q) := by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ ht1 (le_max_left _ _))
      (pow_nonneg (by linarith) _) (by linarith)
  have hd : D*t^q ≤ (C+D)*t^(max p q) := by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ ht1 (le_max_right _ _))
      (pow_nonneg (by linarith) _) (by linarith)
  intro s u hss huu
  exact hop _ _ _ _ (hs s u (hc.trans hss) (hc.trans huu))
    (ht s u (hd.trans hss) (hd.trans huu))

/-- A real polynomial zero test has a polynomially bounded final truth interval. -/
theorem zero_tail (q : Bivariate) : TailStable (fun t s => evaluate q t s = 0) := by
  by_cases hq : q = 0
  · subst q
    simpa [evaluate, specialize] using TailStable.constant True
  · obtain ⟨C,hC,p,hp,ht⟩ := bivariate_eventually_no_roots q hq
    refine ⟨C,hC,p,hp,ht.mono ?_⟩
    intro t h s u hs hu
    simp only [h s hs, h u hu]

/-- A strict sign test has a polynomially bounded final truth interval. -/
theorem positive_tail (q : Bivariate) : TailStable (fun t s => 0 < evaluate q t s) := by
  by_cases hq : q = 0
  · subst q
    simpa [evaluate, specialize] using TailStable.constant False
  · obtain ⟨C,hC,p,hp,ht⟩ := bivariate_eventually_no_roots q hq
    refine ⟨C,hC,p,hp,ht.mono ?_⟩
    intro t h s u hs hu
    exact positive_iff_on_ray _ (specialize q t).continuous _ h s u hs hu

/-- Every genuinely finite sign formula has a polynomially bounded final truth interval. -/
theorem Formula.tail_stable (φ : Formula) : TailStable φ.Holds := by
  induction φ with
  | falsum => exact TailStable.constant False
  | zero q => exact zero_tail q
  | positive q => exact positive_tail q
  | neg φ ih => exact ih.neg
  | conj φ ψ ih jh => exact ih.combine jh And (fun _ _ _ _ => and_congr)
  | disj φ ψ ih jh => exact ih.combine jh Or (fun _ _ _ _ => or_congr)

/-- A nonempty upward-closed fiber described by a finite polynomial sign formula
already contains a point bounded by one polynomial in the parameter. -/
theorem upward_formula_polynomial_bound (φ : Formula)
    (hex : ∀ t, 1 ≤ t → ∃ s, φ.Holds t s)
    (hup : ∀ t s u, 1 ≤ t → s ≤ u → φ.Holds t s → φ.Holds t u) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, 1 ≤ p ∧
      ∀ᶠ t in atTop, φ.Holds t (C*t^p) := by
  obtain ⟨C,hC,p,hp,h⟩ := φ.tail_stable
  refine ⟨C,hC,p,hp,?_⟩
  filter_upwards [h,eventually_ge_atTop (1 : ℝ)] with t ht ht1
  obtain ⟨s,hs⟩ := hex t ht1
  exact (ht (max s (C*t^p)) (C*t^p) (le_max_right _ _) le_rfl).mp
    (hup t s (max s (C*t^p)) ht1 (le_max_left _ _) hs)

/-- Reflection in the second coordinate, implemented by genuine polynomial substitution. -/
def Formula.reflect : Formula → Formula
  | .falsum => .falsum
  | .zero q => .zero (q.comp (-X))
  | .positive q => .positive (q.comp (-X))
  | .neg φ => .neg φ.reflect
  | .conj φ ψ => .conj φ.reflect ψ.reflect
  | .disj φ ψ => .disj φ.reflect ψ.reflect

theorem Formula.reflect_holds (φ : Formula) (t s : ℝ) :
    φ.reflect.Holds t s ↔ φ.Holds t (-s) := by
  induction φ with
  | falsum => rfl
  | zero q => simp [Formula.reflect, Formula.Holds, evaluate, specialize, Polynomial.map_comp]
  | positive q => simp [Formula.reflect, Formula.Holds, evaluate, specialize, Polynomial.map_comp]
  | neg φ ih => exact not_congr ih
  | conj φ ψ ih jh => exact and_congr ih jh
  | disj φ ψ ih jh => exact or_congr ih jh

/-- A single-valued graph cannot enter its formula's constant tail interval. -/
theorem formula_graph_eventual_upper (φ : Formula) (f : ℝ → ℝ)
    (hgraph : ∀ t, 1 ≤ t → ∀ s, φ.Holds t s ↔ s = f t) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, 1 ≤ p ∧ ∀ᶠ t in atTop, f t < C*t^p := by
  obtain ⟨C,hC,p,hp,h⟩ := φ.tail_stable
  refine ⟨C,hC,p,hp,?_⟩
  filter_upwards [h,eventually_ge_atTop (1 : ℝ)] with t ht ht1
  by_contra hn
  have hn' : C*t^p ≤ f t := le_of_not_gt hn
  have hf := (hgraph t ht1 (f t)).mpr rfl
  have hf' := (ht (f t) (f t+1) hn' (by linarith)).mp hf
  have he := (hgraph t ht1 (f t+1)).mp hf'
  linarith

/-- Semialgebraicity of a graph on [1,∞), using the standard finite sign-formula definition. -/
def SemialgebraicGraph (f : ℝ → ℝ) : Prop :=
  ∃ φ : Formula, ∀ t, 1 ≤ t → ∀ s, φ.Holds t s ↔ s = f t

/-- Every semialgebraic graph is polynomially bounded at infinity; no continuity is
needed for this tail statement. -/
theorem semialgebraic_graph_eventual_bound (f : ℝ → ℝ) (h : SemialgebraicGraph f) :
    PolynomialBound f := by
  obtain ⟨φ,hgraph⟩ := h
  obtain ⟨C,hC,p,hp,hf⟩ := formula_graph_eventual_upper φ f hgraph
  have hneg : ∀ t, 1 ≤ t → ∀ s, φ.reflect.Holds t s ↔ s = -f t := by
    intro t ht s
    rw [φ.reflect_holds, hgraph t ht]
    exact neg_eq_iff_eq_neg
  obtain ⟨D,hD,q,hq,hg⟩ := formula_graph_eventual_upper φ.reflect (fun t => -f t) hneg
  refine ⟨C+D, by linarith, max p q, hp.trans (le_max_left _ _), ?_⟩
  filter_upwards [hf,hg,eventually_ge_atTop (1 : ℝ)] with t hf hg ht
  have hc : C*t^p ≤ (C+D)*t^(max p q) :=
    mul_le_mul (by linarith) (pow_le_pow_right₀ ht (le_max_left _ _))
      (pow_nonneg (by linarith) _) (by linarith)
  have hd : D*t^q ≤ (C+D)*t^(max p q) :=
    mul_le_mul (by linarith) (pow_le_pow_right₀ ht (le_max_right _ _))
      (pow_nonneg (by linarith) _) (by linarith)
  apply abs_le.mpr
  constructor <;> linarith

/-- Continuity supplies the missing bound on the compact initial interval. -/
theorem continuous_polynomial_bound (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Ici 1))
    (hb : PolynomialBound f) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, 1 ≤ p ∧ ∀ t, 1 ≤ t → |f t| ≤ C*t^p := by
  obtain ⟨C,hC,p,hp,hb⟩ := hb
  obtain ⟨R,hR⟩ := eventually_atTop.mp hb
  obtain ⟨D,hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.mono (show Set.Icc (1 : ℝ) R ⊆ Set.Ici 1 from fun _ hx => hx.1))
  refine ⟨max C D, hC.trans (le_max_left _ _), p,hp,?_⟩
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  by_cases hRt : R ≤ t
  · exact (hR t hRt).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg ht0 _))
  · have hbound : |f t| ≤ D := by
      simpa only [Real.norm_eq_abs] using hD t ⟨ht,(le_of_not_ge hRt)⟩
    calc
      |f t| ≤ max C D := hbound.trans (le_max_right _ _)
      _ ≤ max C D * t^p := le_mul_of_one_le_right
        (le_trans zero_le_one (hC.trans (le_max_left _ _))) (one_le_pow₀ ht)

/-- The paper's semialgebraic growth lemma, with actual finite real-polynomial graph data.
The input contains no claimed growth bound and no quantifier-elimination oracle. -/
theorem continuous_semialgebraic_growth (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ici 1)) (hg : SemialgebraicGraph f) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ p : ℕ, 1 ≤ p ∧ ∀ t, 1 ≤ t → |f t| ≤ C*t^p :=
  continuous_polynomial_bound f hf (semialgebraic_graph_eventual_bound f hg)

#print axioms continuous_semialgebraic_growth
#print axioms Formula.tail_stable
#print axioms upward_formula_polynomial_bound
#print axioms bivariate_eventually_no_roots
#print axioms positive_iff_on_ray
#print axioms polynomial_ratio_bound
#print axioms root_abs_lt_ratio_sum
end LinearStochastic.SemialgebraicTail
