import LinearStochastic.RealQEFiniteCells
import Mathlib.Data.Finset.Sort
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Order.Hom.Set

/-!
# Ordered finite-cut transport

A polynomial sign table needs the order of roots, not just the unordered set of
realized signs. This file supplies the finite-cut transport and refinement
lemmas needed to assemble local sign-cell reconstruction into such a table.
-/
noncomputable section
namespace LinearStochastic.RealQECutTransport
open Set Polynomial RealQEFiniteCells

/-- Corresponding positions relative to an ordered pair of finite cut sets. -/
def Position {C D : Finset ℝ} (e : C ≃o D) (x y : ℝ) : Prop :=
  ∀ c : C, ((c : ℝ) < x ↔ (e c : ℝ) < y) ∧ (x < (c : ℝ) ↔ y < (e c : ℝ))

theorem Position.symm {C D : Finset ℝ} {e : C ≃o D} {x y : ℝ}
    (h : Position e x y) : Position e.symm y x := by
  intro d
  have hd := h (e.symm d)
  constructor
  · simpa only [e.apply_symm_apply] using hd.1.symm
  · simpa only [e.apply_symm_apply] using hd.2.symm

theorem Position.point {C D : Finset ℝ} (e : C ≃o D) (c : C) :
    Position e c (e c) := by
  intro d
  exact ⟨e.lt_iff_lt.symm,e.lt_iff_lt.symm⟩

theorem Position.eq_of_eq_cut {C D : Finset ℝ} {e : C ≃o D} {x y : ℝ}
    (h : Position e x y) (c : C) (hx : x = c) : y = (e c : ℝ) := by
  have hleft : ¬ (e c : ℝ) < y := by
    rw [← (h c).1,← hx]
    exact lt_irrefl x
  have hright : ¬ y < (e c : ℝ) := by
    rw [← (h c).2,← hx]
    exact lt_irrefl x
  exact le_antisymm (le_of_not_gt hleft) (le_of_not_gt hright)

/-- Every open gap and every cut point has a corresponding real position.
Nonemptiness is constructed using the finite lower/upper bounds. -/
theorem exists_position {C D : Finset ℝ} (e : C ≃o D) (x : ℝ) :
    ∃ y, Position e x y := by
  classical
  by_cases hx : x ∈ C
  · exact ⟨e ⟨x,hx⟩,Position.point e ⟨x,hx⟩⟩
  · let lo : Finset ℝ := (C.attach.filter (fun c : C => (c : ℝ) < x)).image (fun c : C => (e c : ℝ))
    let hi : Finset ℝ := (C.attach.filter (fun c : C => x < (c : ℝ))).image (fun c : C => (e c : ℝ))
    have hcross : ∀ r ∈ lo, ∀ s ∈ hi, r < s := by
      intro r hr s hs
      obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hs
      exact e.strictMono ((Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hd).2)
    obtain ⟨y,hlo,hhi⟩ := Order.exists_between_finsets lo hi hcross
    refine ⟨y,?_⟩
    intro c
    rcases lt_trichotomy (c : ℝ) x with hc | hc | hc
    · have he : (e c : ℝ) < y := hlo _ (Finset.mem_image.mpr
        ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,hc⟩,rfl⟩)
      exact ⟨iff_of_true hc he,iff_of_false (not_lt_of_gt hc) (not_lt_of_gt he)⟩
    · exact False.elim (hx (hc ▸ c.2))
    · have he : y < (e c : ℝ) := hhi _ (Finset.mem_image.mpr
        ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,hc⟩,rfl⟩)
      exact ⟨iff_of_false (not_lt_of_gt hc) (not_lt_of_gt he),iff_of_true hc he⟩

/-- An old cut between two refined points forces the same strict order after transport. -/
theorem Position.lt_of_separator {C D : Finset ℝ} {e : C ≃o D} {x x' y y' : ℝ}
    (h : Position e x y) (h' : Position e x' y') (hxx : x < x')
    (c : C) (hxc : x ≤ c) (hcx : (c : ℝ) ≤ x') : y < y' := by
  rcases hxc.eq_or_lt with hc | hc
  · have hy := h.eq_of_eq_cut c hc
    have hcy' := (h' c).1.mp (by linarith : (c : ℝ) < x')
    simpa only [hy] using hcy'
  · have hyc := (h c).2.mp hc
    have hcy' : (e c : ℝ) ≤ y' := by
      apply le_of_not_gt
      intro he
      have hx'c := (h' c).2.mpr he
      exact not_lt_of_ge hcx hx'c
    exact hyc.trans_le hcy'

/-- A refinement is separated by old cuts when no old open cell receives more
than one new point. Polynomial derivative cuts will establish this condition. -/
def SeparatedBy (C F : Finset ℝ) : Prop :=
  ∀ x ∈ F, ∀ x' ∈ F, x < x' → ∃ c ∈ C, x ≤ c ∧ c ≤ x'

theorem Position.unique_on_refinement {C D F : Finset ℝ} {e : C ≃o D} {x y y' : ℝ}
    (hsep : SeparatedBy D F) (hy : y ∈ F) (hy' : y' ∈ F)
    (h : Position e x y) (h' : Position e x y') : y = y' := by
  apply le_antisymm
  · by_contra hn
    have hlt : y' < y := lt_of_not_ge hn
    obtain ⟨d,hd,hy'd,hdy⟩ := hsep y' hy' y hy hlt
    exact (h'.symm.lt_of_separator h.symm hlt ⟨d,hd⟩ hy'd hdy).false
  · by_contra hn
    have hlt : y < y' := lt_of_not_ge hn
    obtain ⟨d,hd,hyd,hdy'⟩ := hsep y hy y' hy' hlt
    exact (h.symm.lt_of_separator h'.symm hlt ⟨d,hd⟩ hyd hdy').false

/-- Local existence in both directions, plus separation by old cuts, assembles
into an actual order isomorphism of the refined finite cut sets. -/
def refineOrderIso {C D F G : Finset ℝ} (e : C ≃o D)
    (hF : SeparatedBy C F) (hG : SeparatedBy D G)
    (hforward : ∀ x ∈ F, ∃ y ∈ G, Position e x y)
    (hback : ∀ y ∈ G, ∃ x ∈ F, Position e x y) : F ≃o G := by
  let f : F → G := fun x =>
    ⟨Classical.choose (hforward x x.2),(Classical.choose_spec (hforward x x.2)).1⟩
  have hf : ∀ x : F, Position e x (f x) := fun x => (Classical.choose_spec (hforward x x.2)).2
  have hmono : StrictMono f := by
    intro x x' hxx
    obtain ⟨c,hc,hxc,hcx⟩ := hF x x.2 x' x'.2 hxx
    exact (hf x).lt_of_separator (hf x') hxx ⟨c,hc⟩ hxc hcx
  have hsur : Function.Surjective f := by
    intro y
    obtain ⟨x,hx,hxy⟩ := hback y y.2
    refine ⟨⟨x,hx⟩,Subtype.ext ?_⟩
    exact Position.unique_on_refinement hG (f ⟨x,hx⟩).2 y.2 (hf ⟨x,hx⟩) hxy
  exact StrictMono.orderIsoOfSurjective f hmono hsur

/-- The assembled order isomorphism satisfies the original local correspondence. -/
theorem refineOrderIso_position {C D F G : Finset ℝ} (e : C ≃o D)
    (hF : SeparatedBy C F) (hG : SeparatedBy D G)
    (hforward : ∀ x ∈ F, ∃ y ∈ G, Position e x y)
    (hback : ∀ y ∈ G, ∃ x ∈ F, Position e x y) (x : F) :
    Position e x (refineOrderIso e hF hG hforward hback x) := by
  exact (Classical.choose_spec (hforward x x.2)).2

/-- Dropping auxiliary cut points gives an actual restricted order isomorphism. -/
def restrictOrderIso {C D F G : Finset ℝ} (e : C ≃o D)
    (hF : F ⊆ C) (hG : G ⊆ D)
    (hmem : ∀ c : C, ((c : ℝ) ∈ F ↔ (e c : ℝ) ∈ G)) : F ≃o G := by
  let f : F → G := fun x => ⟨e ⟨x,hF x.2⟩,(hmem ⟨x,hF x.2⟩).mp x.2⟩
  have hmono : StrictMono f := by
    intro x y hxy
    exact e.strictMono hxy
  have hsur : Function.Surjective f := by
    intro y
    let x : C := e.symm ⟨y,hG y.2⟩
    have hx : (x : ℝ) ∈ F := (hmem x).mpr (by
      change (e (e.symm ⟨y,hG y.2⟩) : ℝ) ∈ G
      simpa only [e.apply_symm_apply] using y.2)
    refine ⟨⟨x,hx⟩,Subtype.ext ?_⟩
    change (e (e.symm ⟨y,hG y.2⟩) : ℝ) = (y : ℝ)
    exact congrArg (fun z : D => (z : ℝ)) (e.apply_symm_apply ⟨y,hG y.2⟩)
  exact StrictMono.orderIsoOfSurjective f hmono hsur

theorem Position.restrict {C D F G : Finset ℝ} {e : C ≃o D}
    (hF : F ⊆ C) (hG : G ⊆ D)
    (hmem : ∀ c : C, ((c : ℝ) ∈ F ↔ (e c : ℝ) ∈ G))
    {x y : ℝ} (h : Position e x y) : Position (restrictOrderIso e hF hG hmem) x y := by
  intro c
  exact h ⟨c,hF c.2⟩

/-- Positions compose, so a common source position gives one common target cell. -/
theorem Position.trans {C D E : Finset ℝ} {e : C ≃o D} {e' : D ≃o E}
    {x y z : ℝ} (h : Position e x y) (h' : Position e' y z) :
    Position (e.trans e') x z := by
  intro c
  exact ⟨(h c).1.trans (h' (e c)).1,(h c).2.trans (h' (e c)).2⟩

/-- The exact root cuts determine constant signs on every position class,
including singleton cut points and all unbounded gaps. -/
theorem same_position_signs (qs : List ℝ[X]) {x y : ℝ}
    (h : Position (OrderIso.refl (rootCuts qs)) x y) :
    ∀ P ∈ qs, SameSign (P.eval x) (P.eval y) := by
  classical
  by_cases hx : x ∈ rootCuts qs
  · have hy : y = x := h.eq_of_eq_cut ⟨x,hx⟩ rfl
    subst y
    exact fun P _ => SameSign.refl (P.eval x)
  · let lower := (rootCuts qs).filter (fun r => r < x)
    have hgap := noncut_mem_gap (rootCuts qs) x hx
    have hygap : y ∈ gap (rootCuts qs) lower := by
      constructor
      · intro r hr
        have hr' := Finset.mem_filter.mp hr
        exact (h ⟨r,hr'.1⟩).1.mp hr'.2
      · intro r hr
        have hr' := Finset.mem_sdiff.mp hr
        exact (h ⟨r,hr'.1⟩).2.mp (hgap.2 r hr)
    intro P hP
    exact gap_signs qs lower P hP hgap hygap

/-- Exact ordered sign-table equivalence. The invariant includes root order and
all point/gap signs; it is deliberately stronger than unordered realizable signs. -/
structure SignTableEquivalence (ps qs : List ℝ[X]) where
  cuts : rootCuts ps ≃o rootCuts qs
  signs : ∀ x y, Position cuts x y →
    List.Forall₂ (fun P Q => SameSign (P.eval x) (Q.eval y)) ps qs

/-- Any ordered table equivalence transports a real witness with its entire sign vector. -/
theorem SignTableEquivalence.exists_signs {ps qs : List ℝ[X]}
    (h : SignTableEquivalence ps qs) (x : ℝ) :
    ∃ y, List.Forall₂ (fun P Q => SameSign (P.eval x) (Q.eval y)) ps qs := by
  obtain ⟨y,hy⟩ := exists_position h.cuts x
  exact ⟨y,h.signs x y hy⟩

theorem rootCuts_cons (P : ℝ[X]) (ps : List ℝ[X]) :
    rootCuts (P :: ps) = P.roots.toFinset ∪ rootCuts ps := by
  classical
  simp only [rootCuts,List.toFinset_cons,Finset.biUnion_insert]

theorem roots_membership_iff_of_signs {ps qs : List ℝ[X]} {x y : ℝ}
    (hzero : List.Forall₂ (fun P Q => (P = 0 ↔ Q = 0)) ps qs)
    (hsigns : List.Forall₂ (fun P Q => SameSign (P.eval x) (Q.eval y)) ps qs) :
    x ∈ rootCuts ps ↔ y ∈ rootCuts qs := by
  induction hzero with
  | nil => simp [rootCuts]
  | @cons P Q ps qs hzero htail ih =>
    cases hsigns with
    | cons hhead hrest =>
      simp only [rootCuts_cons,Finset.mem_union,Multiset.mem_toFinset,
        Polynomial.mem_roots',Polynomial.IsRoot]
      exact or_congr (and_congr (not_congr hzero) hhead.1) (ih hrest)

theorem forall₂_signs_trans {ps qs : List ℝ[X]} {x y z : ℝ}
    (hsigns : List.Forall₂ (fun P Q => SameSign (P.eval x) (Q.eval y)) ps qs)
    (hsame : ∀ Q ∈ qs, SameSign (Q.eval y) (Q.eval z)) :
    List.Forall₂ (fun P Q => SameSign (P.eval x) (Q.eval z)) ps qs := by
  induction hsigns with
  | nil => exact List.Forall₂.nil
  | @cons P Q ps qs hhead htail ih =>
    exact List.Forall₂.cons (hhead.trans (hsame Q (by simp)))
      (ih (fun R hR => hsame R (List.mem_cons_of_mem _ hR)))

/-- Auxiliary derivative/remainder roots may be removed after refinement.
This proves the important pruning step: the result again uses *exactly* the
original family's roots, so future recursive boundary arguments stay justified. -/
def pruneSignTable (ps qs : List ℝ[X]) (C D : Finset ℝ) (e : C ≃o D)
    (hC : rootCuts ps ⊆ C) (hD : rootCuts qs ⊆ D)
    (hzero : List.Forall₂ (fun P Q => (P = 0 ↔ Q = 0)) ps qs)
    (hsigns : ∀ x y, Position e x y →
      List.Forall₂ (fun P Q => SameSign (P.eval x) (Q.eval y)) ps qs) :
    SignTableEquivalence ps qs := by
  have hmem : ∀ c : C, ((c : ℝ) ∈ rootCuts ps ↔ (e c : ℝ) ∈ rootCuts qs) := by
    intro c
    exact roots_membership_iff_of_signs hzero (hsigns c (e c) (Position.point e c))
  let e' := restrictOrderIso e hC hD hmem
  refine ⟨e',?_⟩
  intro x y hxy
  obtain ⟨z,hxz⟩ := exists_position e x
  have hxz' : Position e' x z := hxz.restrict hC hD hmem
  have hzy : Position (OrderIso.refl (rootCuts qs)) z y := by
    intro d
    have hz := hxz' (e'.symm d)
    have hy := hxy (e'.symm d)
    change ((d : ℝ) < z ↔ (d : ℝ) < y) ∧ (z < (d : ℝ) ↔ y < (d : ℝ))
    constructor
    · simpa only [e'.apply_symm_apply] using hz.1.symm.trans hy.1
    · simpa only [e'.apply_symm_apply] using hz.2.symm.trans hy.2
  exact forall₂_signs_trans (hsigns x z hxz) (same_position_signs qs hzy)

#print axioms pruneSignTable
/-- Distinct roots of the new polynomial are separated by actual derivative
roots (Rolle). Thus adding its roots contributes at most one point per old gap. -/
theorem polynomial_roots_separated (C : Finset ℝ) (P : ℝ[X])
    (hderiv : P.derivative ≠ 0)
    (hcuts : ∀ c ∈ P.derivative.roots.toFinset, c ∈ C) :
    SeparatedBy C (C ∪ P.roots.toFinset) := by
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx
  · exact ⟨x,hx,le_rfl,hxy.le⟩
  · rcases Finset.mem_union.mp hy with hy | hy
    · exact ⟨y,hy,hxy.le,le_rfl⟩
    · have hPx : P.eval x = 0 := (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp hx)).2
      have hPy : P.eval y = 0 := (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp hy)).2
      obtain ⟨c,hc,hderivc⟩ := exists_deriv_eq_zero hxy P.continuous.continuousOn (hPx.trans hPy.symm)
      have hcroot : c ∈ P.derivative.roots.toFinset := by
        apply Multiset.mem_toFinset.mpr
        apply (Polynomial.mem_roots hderiv).mpr
        simpa only [Polynomial.deriv,Polynomial.IsRoot] using hderivc
      exact ⟨c,hcuts c hcroot,hc.1.le,hc.2.le⟩

#print axioms same_position_signs
#print axioms restrictOrderIso
#print axioms polynomial_roots_separated
#print axioms exists_position
#print axioms refineOrderIso
#print axioms refineOrderIso_position
end LinearStochastic.RealQECutTransport
