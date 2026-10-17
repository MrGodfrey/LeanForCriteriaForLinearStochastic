module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Polynomial sign-cell reconstruction primitives

These are the high-degree interpolation steps used after lower-degree derivative
and remainder signs are known. They prove actual root existence, uniqueness and
signs on every point of the refined cell. They do not assert the missing uniform
parameter projection or a complete quantifier-elimination algorithm.
-/
noncomputable section
namespace LinearStochastic.RealQESignCells
open Polynomial Set

/-- The derivative is a genuinely smaller polynomial in the degree recursion. -/
theorem derivative_degree_drop (P : ℝ[X]) (hP : P ≠ 0) : P.derivative.degree < P.degree :=
  Polynomial.degree_derivative_lt hP

/-- Positive derivative signs on an open cell imply strict monotonicity up to both endpoints. -/
theorem strictMonoOn_cell (P : ℝ[X]) (a b : ℝ)
    (hd : ∀ x ∈ Ioo a b, 0 < P.derivative.eval x) : StrictMonoOn P.eval (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) P.continuous.continuousOn
  intro x hx
  rw [interior_Icc] at hx
  simpa only [Polynomial.deriv] using hd x hx

/-- Endpoints with opposite signs force exactly one interior root, because the
lower-degree derivative has fixed positive sign throughout the cell. -/
theorem increasing_cell_root_iff (P : ℝ[X]) (a b : ℝ) (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, 0 < P.derivative.eval x) :
    (∃! x, x ∈ Ioo a b ∧ P.eval x = 0) ↔ P.eval a < 0 ∧ 0 < P.eval b := by
  have hm := strictMonoOn_cell P a b hd
  constructor
  · rintro ⟨x,⟨hx,hz⟩,_⟩
    constructor
    · have h := hm (left_mem_Icc.mpr hab.le) ⟨hx.1.le,hx.2.le⟩ hx.1
      simpa only [hz] using h
    · have h := hm ⟨hx.1.le,hx.2.le⟩ (right_mem_Icc.mpr hab.le) hx.2
      simpa only [hz] using h
  · rintro ⟨ha,hb⟩
    obtain ⟨x,hx,hz⟩ := intermediate_value_Icc hab.le P.continuous.continuousOn
      (show 0 ∈ Icc (P.eval a) (P.eval b) from ⟨ha.le,hb.le⟩)
    have hax : a < x := lt_of_le_of_ne hx.1 (by intro h; subst x; linarith)
    have hxb : x < b := lt_of_le_of_ne hx.2 (by intro h; subst x; linarith)
    refine ⟨x,⟨⟨hax,hxb⟩,hz⟩,?_⟩
    intro y hy
    exact hm.injOn ⟨hy.1.1.le,hy.1.2.le⟩ hx (hy.2.trans hz.symm)

/-- Once the unique root is inserted, signs on its two adjacent subcells are forced. -/
theorem increasing_cell_root_signs (P : ℝ[X]) (a b r : ℝ)
    (hd : ∀ x ∈ Ioo a b, 0 < P.derivative.eval x)
    (hr : r ∈ Ioo a b) (hroot : P.eval r = 0) :
    (∀ x ∈ Ioo a r, P.eval x < 0) ∧ (∀ x ∈ Ioo r b, 0 < P.eval x) := by
  have hm := strictMonoOn_cell P a b hd
  constructor
  · intro x hx
    have h := hm ⟨hx.1.le,(hx.2.trans hr.2).le⟩ ⟨hr.1.le,hr.2.le⟩ hx.2
    simpa only [hroot] using h
  · intro x hx
    have h := hm ⟨hr.1.le,hr.2.le⟩ ⟨(hr.1.trans hx.1).le,hx.2.le⟩ hx.1
    simpa only [hroot] using h

/-- The exhaustive reconstruction of a bounded cell from lower-degree derivative
sign and the dividend's two endpoint signs. No unproved sign-table oracle is used. -/
theorem increasing_cell_trichotomy (P : ℝ[X]) (a b : ℝ) (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, 0 < P.derivative.eval x) :
    (0 ≤ P.eval a ∧ ∀ x ∈ Ioo a b, 0 < P.eval x) ∨
    (P.eval b ≤ 0 ∧ ∀ x ∈ Ioo a b, P.eval x < 0) ∨
    (P.eval a < 0 ∧ 0 < P.eval b ∧
      ∃ r ∈ Ioo a b, P.eval r = 0 ∧
        (∀ x ∈ Ioo a r, P.eval x < 0) ∧
        (∀ x ∈ Ioo r b, 0 < P.eval x) ∧
        (∀ x ∈ Ioo a b, P.eval x = 0 → x = r)) := by
  have hm := strictMonoOn_cell P a b hd
  by_cases ha : 0 ≤ P.eval a
  · left
    refine ⟨ha,?_⟩
    intro x hx
    exact ha.trans_lt (hm (left_mem_Icc.mpr hab.le) ⟨hx.1.le,hx.2.le⟩ hx.1)
  · right
    by_cases hb : P.eval b ≤ 0
    · left
      refine ⟨hb,?_⟩
      intro x hx
      exact (hm ⟨hx.1.le,hx.2.le⟩ (right_mem_Icc.mpr hab.le) hx.2).trans_le hb
    · right
      have ha' : P.eval a < 0 := lt_of_not_ge ha
      have hb' : 0 < P.eval b := lt_of_not_ge hb
      obtain ⟨r,⟨hr,hroot⟩,hunique⟩ := (increasing_cell_root_iff P a b hab hd).mpr ⟨ha',hb'⟩
      obtain ⟨hl,hright⟩ := increasing_cell_root_signs P a b r hd hr hroot
      exact ⟨ha',hb',r,hr,hroot,hl,hright,fun x hx hz => hunique x ⟨hx,hz⟩⟩

/-- Negative derivative cells are handled by negating the actual polynomial. -/
theorem decreasing_cell_root_iff (P : ℝ[X]) (a b : ℝ) (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, P.derivative.eval x < 0) :
    (∃! x, x ∈ Ioo a b ∧ P.eval x = 0) ↔ 0 < P.eval a ∧ P.eval b < 0 := by
  have h := increasing_cell_root_iff (-P) a b hab (by
    intro x hx
    simpa only [Polynomial.derivative_neg, Polynomial.eval_neg, neg_pos] using hd x hx)
  simpa only [Polynomial.eval_neg, neg_eq_zero, neg_lt_zero, neg_pos] using h

/-- The sign at positive infinity is fixed by the actual leading coefficient. -/
theorem positive_infinity_signs (P : ℝ[X]) :
    ∀ᶠ x in Filter.atTop, (P.eval x = 0 ↔ P = 0) ∧
      (0 < P.eval x ↔ 0 < P.leadingCoeff) := by
  by_cases hP : P = 0
  · subst P
    simp
  have hl : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  rcases lt_or_gt_of_ne hl with hl | hl
  · have h := P.isEquivalent_atTop_lead.eventually_neg (by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      exact mul_neg_of_neg_of_pos hl (pow_pos hx _))
    filter_upwards [h] with x hx
    simp [ne_of_lt hx, hP, not_lt_of_gt hx, not_lt_of_gt hl]
  · have h := P.isEquivalent_atTop_lead.eventually_pos (by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      exact mul_pos hl (pow_pos hx _))
    filter_upwards [h] with x hx
    simp [ne_of_gt hx, hP, hx, hl]

/-- The negative-infinity sign is obtained by the actual polynomial substitution X↦−X. -/
theorem negative_infinity_signs (P : ℝ[X]) :
    ∀ᶠ x in Filter.atTop,
      (P.eval (-x) = 0 ↔ P.comp (-Polynomial.X) = 0) ∧
      (0 < P.eval (-x) ↔ 0 < (P.comp (-Polynomial.X)).leadingCoeff) := by
  simpa only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X] using
    positive_infinity_signs (P.comp (-Polynomial.X))

/-- Reconstruct the right unbounded cell, with the infinity sign proved from coefficients. -/
theorem increasing_right_cell_root_iff (P : ℝ[X]) (a : ℝ)
    (hd : ∀ x, a < x → 0 < P.derivative.eval x)
    (hlead : 0 < P.leadingCoeff) :
    (∃! x, a < x ∧ P.eval x = 0) ↔ P.eval a < 0 := by
  have hm : StrictMonoOn P.eval (Ici a) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici a) P.continuous.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    simpa only [Polynomial.deriv] using hd x hx
  constructor
  · rintro ⟨x,⟨hx,hz⟩,_⟩
    have h := hm (show a ∈ Ici a from Set.mem_Ici.mpr (le_refl a)) (show x ∈ Ici a from hx.le) hx
    simpa only [hz] using h
  · intro ha
    have hev : ∀ᶠ b in Filter.atTop, a < b ∧ 0 < P.eval b := by
      filter_upwards [positive_infinity_signs P, Filter.eventually_gt_atTop a] with b hb hab
      exact ⟨hab,hb.2.mpr hlead⟩
    obtain ⟨b,hab,hb⟩ := hev.exists
    obtain ⟨r,⟨hr,hroot⟩,_⟩ := (increasing_cell_root_iff P a b hab
      (fun x hx => hd x hx.1)).mpr ⟨ha,hb⟩
    refine ⟨r,⟨hr.1,hroot⟩,?_⟩
    intro x hx
    exact hm.injOn hx.1.le hr.1.le (hx.2.trans hroot.symm)

#print axioms positive_infinity_signs
#print axioms increasing_right_cell_root_iff
#print axioms increasing_cell_trichotomy
#print axioms decreasing_cell_root_iff
end LinearStochastic.RealQESignCells
