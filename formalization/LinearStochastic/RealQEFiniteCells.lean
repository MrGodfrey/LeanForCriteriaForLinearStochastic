module

public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.CountableDenseLinearOrder
public import Mathlib.Tactic

@[expose] public section

/-!
# Actual finite sign cells for real polynomial families

The cuts are precisely the union of roots of the nonzero input polynomials.
Every real point is represented by a finite sign table, with all input signs
constant on each cell. Samples are chosen as real numbers; this alone is not a
uniform symbolic projection or quantifier-elimination theorem.
-/
noncomputable section
namespace LinearStochastic.RealQEFiniteCells
open Polynomial Set

/-- Zero and positivity determine all three real signs. -/
def SameSign (x y : ℝ) : Prop := (x = 0 ↔ y = 0) ∧ (0 < x ↔ 0 < y)

@[refl] theorem SameSign.refl (x : ℝ) : SameSign x x := ⟨Iff.rfl,Iff.rfl⟩
theorem SameSign.symm {x y : ℝ} (h : SameSign x y) : SameSign y x := ⟨h.1.symm,h.2.symm⟩
theorem SameSign.trans {x y z : ℝ} (h : SameSign x y) (k : SameSign y z) : SameSign x z :=
  ⟨h.1.trans k.1,h.2.trans k.2⟩
theorem SameSign.neg_iff {x y : ℝ} (h : SameSign x y) : x < 0 ↔ y < 0 := by
  constructor <;> intro hn
  · by_contra hy
    have hnon : 0 ≤ y := le_of_not_gt hy
    rcases hnon.eq_or_lt with hz | hp
    · have := h.1.mpr hz.symm
      linarith
    · have := h.2.mpr hp
      linarith
  · by_contra hx
    have hnon : 0 ≤ x := le_of_not_gt hx
    rcases hnon.eq_or_lt with hz | hp
    · have := h.1.mp hz.symm
      linarith
    · have := h.2.mp hp
      linarith

theorem SameSign.neg {x y : ℝ} (h : SameSign x y) : SameSign (-x) (-y) := by
  constructor
  · simpa only [neg_eq_zero] using h.1
  · simpa only [neg_pos] using h.neg_iff

theorem SameSign.mul_left {x y : ℝ} (h : SameSign x y) (c : ℝ) : SameSign (c*x) (c*y) := by
  constructor
  · simp only [mul_eq_zero]
    exact or_congr Iff.rfl h.1
  · simp only [mul_pos_iff]
    exact or_congr (and_congr Iff.rfl h.2) (and_congr Iff.rfl h.neg_iff)

/-- The finite cut set contains every root of every nonzero input polynomial. -/
def rootCuts (qs : List ℝ[X]) : Finset ℝ := by
  classical
  exact qs.toFinset.biUnion (fun P => P.roots.toFinset)

theorem mem_rootCuts (qs : List ℝ[X]) (x : ℝ) :
    x ∈ rootCuts qs ↔ ∃ P ∈ qs, P ≠ 0 ∧ P.eval x = 0 := by
  classical
  simp only [rootCuts,Finset.mem_biUnion,List.mem_toFinset,Multiset.mem_toFinset,
    Polynomial.mem_roots',Polynomial.IsRoot]

/-- A gap is specified by the subset of cuts to its left. Empty candidates are
allowed, so all gaps are indexed by the finite powerset of the actual cuts. -/
def gap (cuts lower : Finset ℝ) : Set ℝ :=
  {x | (∀ r ∈ lower, r < x) ∧ ∀ r ∈ cuts \ lower, x < r}

theorem gap_ordConnected (cuts lower : Finset ℝ) : (gap cuts lower).OrdConnected := by
  apply Set.ordConnected_iff.mpr
  intro x hx y hy hxy z hz
  exact ⟨fun r hr => (hx.1 r hr).trans_le hz.1,
    fun r hr => hz.2.trans_lt (hy.2 r hr)⟩

theorem gap_nonempty_iff (cuts lower : Finset ℝ) :
    (gap cuts lower).Nonempty ↔ ∀ r ∈ lower, ∀ s ∈ cuts \ lower, r < s := by
  constructor
  · rintro ⟨x,hx⟩ r hr s hs
    exact (hx.1 r hr).trans (hx.2 s hs)
  · intro h
    exact Order.exists_between_finsets lower (cuts \ lower) h

theorem gap_disjoint_cuts (cuts lower : Finset ℝ) (x : ℝ) (hx : x ∈ gap cuts lower) :
    x ∉ cuts := by
  classical
  intro hcut
  by_cases hl : x ∈ lower
  · exact (hx.1 x hl).false
  · exact (hx.2 x (Finset.mem_sdiff.mpr ⟨hcut,hl⟩)).false

theorem noncut_mem_gap (cuts : Finset ℝ) (x : ℝ) (hx : x ∉ cuts) :
    x ∈ gap cuts (cuts.filter (fun r => r < x)) := by
  classical
  constructor
  · intro r hr
    exact (Finset.mem_filter.mp hr).2
  · intro r hr
    obtain ⟨hcut,hn⟩ := Finset.mem_sdiff.mp hr
    have hnlt : ¬ r < x := by intro h; exact hn (Finset.mem_filter.mpr ⟨hcut,h⟩)
    exact lt_of_le_of_ne (le_of_not_gt hnlt) (by intro h; subst r; exact hx hcut)

/-- No-root connected cells have a constant real sign, proved by the intermediate value theorem. -/
theorem sameSign_of_no_roots (P : ℝ[X]) (s : Set ℝ) (hs : IsPreconnected s)
    (hz : ∀ x ∈ s, P.eval x ≠ 0) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    SameSign (P.eval x) (P.eval y) := by
  constructor
  · simp [hz x hx,hz y hy]
  · constructor
    · intro hxp
      by_contra hyp
      have hyn : P.eval y < 0 := lt_of_le_of_ne (le_of_not_gt hyp) (hz y hy)
      obtain ⟨z,hzmem,hroot⟩ := hs.intermediate_value hy hx P.continuous.continuousOn
        (show 0 ∈ Icc (P.eval y) (P.eval x) from ⟨hyn.le,hxp.le⟩)
      exact hz z hzmem hroot
    · intro hyp
      by_contra hxp
      have hxn : P.eval x < 0 := lt_of_le_of_ne (le_of_not_gt hxp) (hz x hx)
      obtain ⟨z,hzmem,hroot⟩ := hs.intermediate_value hx hy P.continuous.continuousOn
        (show 0 ∈ Icc (P.eval x) (P.eval y) from ⟨hxn.le,hyp.le⟩)
      exact hz z hzmem hroot

/-- Every polynomial in the input list has constant sign throughout each gap. -/
theorem gap_signs (qs : List ℝ[X]) (lower : Finset ℝ) (P : ℝ[X]) (hP : P ∈ qs)
    {x y : ℝ} (hx : x ∈ gap (rootCuts qs) lower) (hy : y ∈ gap (rootCuts qs) lower) :
    SameSign (P.eval x) (P.eval y) := by
  by_cases hzero : P = 0
  · subst P
    simpa only [Polynomial.eval_zero] using SameSign.refl 0
  · apply sameSign_of_no_roots P _ (gap_ordConnected _ _).isPreconnected _ hx hy
    intro z hz hroot
    exact gap_disjoint_cuts _ _ z hz ((mem_rootCuts qs z).mpr ⟨P,hP,hzero,hroot⟩)

/-- One chosen representative per gap candidate; empty candidates contribute 0.
Every representative is a real point, so the extra 0 causes no spurious witnesses. -/
def gapSample (cuts lower : Finset ℝ) : ℝ := by
  classical
  exact if h : (gap cuts lower).Nonempty then Classical.choose h else 0

theorem gapSample_mem (cuts lower : Finset ℝ) (h : (gap cuts lower).Nonempty) :
    gapSample cuts lower ∈ gap cuts lower := by
  simp only [gapSample,dif_pos h]
  exact Classical.choose_spec h

def samples (qs : List ℝ[X]) : Finset ℝ := by
  classical
  exact rootCuts qs ∪ (rootCuts qs).powerset.image (gapSample (rootCuts qs))

/-- A finite table represents every sign vector occurring anywhere on the real line. -/
theorem finite_sign_table_complete (qs : List ℝ[X]) (x : ℝ) :
    ∃ y ∈ samples qs, ∀ P ∈ qs, SameSign (P.eval x) (P.eval y) := by
  classical
  by_cases hx : x ∈ rootCuts qs
  · exact ⟨x,Finset.mem_union_left _ hx,fun P _ => SameSign.refl (P.eval x)⟩
  · let lower := (rootCuts qs).filter (fun r => r < x)
    have hgap : x ∈ gap (rootCuts qs) lower := noncut_mem_gap _ x hx
    refine ⟨gapSample (rootCuts qs) lower,?_,?_⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨lower,Finset.mem_powerset.mpr (Finset.filter_subset _ _),rfl⟩)
    · intro P hP
      exact gap_signs qs lower P hP hgap (gapSample_mem _ _ ⟨x,hgap⟩)

/-- Any predicate depending only on the input polynomial signs has an actual
finite disjunction of witnesses. This is real-sample semantics, not polynomial projection. -/
theorem exists_iff_finite_samples (qs : List ℝ[X]) (F : ℝ → Prop)
    (hF : ∀ x y, (∀ P ∈ qs, SameSign (P.eval x) (P.eval y)) → (F x ↔ F y)) :
    (∃ x, F x) ↔ ∃ y ∈ samples qs, F y := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨y,hy,hs⟩ := finite_sign_table_complete qs x
    exact ⟨y,hy,(hF x y hs).mp hx⟩
  · rintro ⟨y,_,hy⟩
    exact ⟨y,hy⟩

#print axioms gap_signs
#print axioms finite_sign_table_complete
#print axioms exists_iff_finite_samples
end LinearStochastic.RealQEFiniteCells
