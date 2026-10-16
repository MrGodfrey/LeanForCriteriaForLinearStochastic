import LinearStochastic.RealQEGapIntervals

/-!
# Refining an ordered sign table by one polynomial

This assembles the proved local interpolation and Rolle separation into an
ordered correspondence of all old and new root cuts. Further lemmas establish
signs on the resulting position classes before auxiliary cuts are pruned.
-/
noncomputable section
namespace LinearStochastic.RealQETableRefinement
open Polynomial Set RealQEFiniteCells RealQECutTransport RealQEGapIntervals

/-- A value/sign correspondence carries a source refined cut to a target refined cut. -/
theorem refined_cut_mem {C D : Finset ℝ} {e : C ≃o D} (P Q : ℝ[X])
    (hQ : Q ≠ 0) {x y : ℝ} (hx : x ∈ C ∪ P.roots.toFinset)
    (hpos : Position e x y) (hs : SameSign (P.eval x) (Q.eval y)) :
    y ∈ D ∪ Q.roots.toFinset := by
  classical
  rcases Finset.mem_union.mp hx with hx | hx
  · have hy := hpos.eq_of_eq_cut ⟨x,hx⟩ rfl
    exact Finset.mem_union_left _ (hy ▸ (e ⟨x,hx⟩).2)
  · apply Finset.mem_union_right
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hQ).mpr
    exact hs.1.mp (Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp hx)).2

structure RefinedCuts {C D : Finset ℝ} (e : C ≃o D) (P Q : ℝ[X]) where
  cuts : ↥(C ∪ P.roots.toFinset) ≃o ↥(D ∪ Q.roots.toFinset)
  positions : ∀ c : ↥(C ∪ P.roots.toFinset), Position e c (cuts c)
  signs : ∀ c : ↥(C ∪ P.roots.toFinset), SameSign (P.eval c) (Q.eval (cuts c))

/-- No root-order oracle is assumed: it is assembled from both local witness
directions and the actual derivative-root separation proved by Rolle. -/
def refinePolynomialCuts {C D : Finset ℝ} (e : C ≃o D) (P Q : ℝ[X])
    (hP : P.derivative ≠ 0) (hQ : Q.derivative ≠ 0)
    (hPC : ∀ r ∈ P.derivative.roots.toFinset, r ∈ C)
    (hQD : ∀ r ∈ Q.derivative.roots.toFinset, r ∈ D)
    (hforward : ∀ x, ∃ y, Position e x y ∧ SameSign (P.eval x) (Q.eval y))
    (hback : ∀ y, ∃ x, Position e x y ∧ SameSign (P.eval x) (Q.eval y)) :
    RefinedCuts e P Q := by
  have hPn : P ≠ 0 := by intro h; subst P; simp at hP
  have hQn : Q ≠ 0 := by intro h; subst Q; simp at hQ
  have hsepP := polynomial_roots_separated C P hP hPC
  have hsepQ := polynomial_roots_separated D Q hQ hQD
  have hfw : ∀ x ∈ C ∪ P.roots.toFinset, ∃ y ∈ D ∪ Q.roots.toFinset, Position e x y := by
    intro x hx
    obtain ⟨y,hy,hs⟩ := hforward x
    exact ⟨y,refined_cut_mem P Q hQn hx hy hs,hy⟩
  have hbw : ∀ y ∈ D ∪ Q.roots.toFinset, ∃ x ∈ C ∪ P.roots.toFinset, Position e x y := by
    intro y hy
    obtain ⟨x,hx,hs⟩ := hback y
    exact ⟨x,refined_cut_mem Q P hPn hy hx.symm hs.symm,hx⟩
  let e' := refineOrderIso e hsepP hsepQ hfw hbw
  have he' : ∀ c : ↥(C ∪ P.roots.toFinset), Position e c (e' c) := refineOrderIso_position e hsepP hsepQ hfw hbw
  refine ⟨e',he',?_⟩
  intro c
  obtain ⟨y,hy,hs⟩ := hforward c
  have hym := refined_cut_mem P Q hQn c.2 hy hs
  have heq : (e' c : ℝ) = y := Position.unique_on_refinement hsepQ (e' c).2 hym (he' c) hy
  simpa only [heq] using hs

/-- The actual lower-degree hypotheses supply both local witness directions. -/
def polynomialRefinement {C D : Finset ℝ} (e : C ≃o D) (P Q : ℝ[X])
    (hP : P.derivative ≠ 0) (hQ : Q.derivative ≠ 0)
    (hPC : ∀ r ∈ P.derivative.roots.toFinset, r ∈ C)
    (hQD : ∀ r ∈ Q.derivative.roots.toFinset, r ∈ D)
    (hderiv : ∀ x y, Position e x y → SameSign (P.derivative.eval x) (Q.derivative.eval y))
    (hpoints : ∀ c : C, SameSign (P.eval c) (Q.eval (e c)))
    (hlead : SameSign P.leadingCoeff Q.leadingCoeff)
    (hreflect : SameSign (P.comp (-X)).leadingCoeff (Q.comp (-X)).leadingCoeff) :
    RefinedCuts e P Q := by
  apply refinePolynomialCuts e P Q hP hQ hPC hQD
  · exact polynomial_position_transfer e P Q hP hPC hderiv hpoints hlead hreflect
  · intro y
    obtain ⟨x,hx,hs⟩ := polynomial_position_transfer e.symm Q P hQ hQD
      (fun u v h => (hderiv v u h.symm).symm)
      (by intro d; simpa only [e.apply_symm_apply] using (hpoints (e.symm d)).symm)
      hlead.symm hreflect.symm y
    exact ⟨x,hx.symm,hs.symm⟩

/-- Every old cut is fixed to its prescribed old correspondent. -/
theorem RefinedCuts.old_cut {C D : Finset ℝ} {e : C ≃o D} {P Q : ℝ[X]}
    (r : RefinedCuts e P Q) (c : C) :
    (r.cuts ⟨c,Finset.mem_union_left _ c.2⟩ : ℝ) = (e c : ℝ) :=
  (r.positions ⟨c,Finset.mem_union_left _ c.2⟩).eq_of_eq_cut c rfl

/-- A refined point/gap correspondence also preserves the old cut position. -/
theorem RefinedCuts.base_position {C D : Finset ℝ} {e : C ≃o D} {P Q : ℝ[X]}
    (r : RefinedCuts e P Q) {x y : ℝ} (h : Position r.cuts x y) : Position e x y := by
  intro c
  have hc := h ⟨c,Finset.mem_union_left _ c.2⟩
  simpa only [r.old_cut c] using hc

/-- The refined position classes are convex, including singleton root classes. -/
theorem position_ordConnected {C D : Finset ℝ} (e : C ≃o D) (x : ℝ) :
    {y | Position e x y}.OrdConnected := by
  apply Set.ordConnected_iff.mpr
  intro y hy z hz hyz t ht c
  constructor
  · exact ⟨fun hc => ((hy c).1.mp hc).trans_le ht.1,
      fun hc => (hz c).1.mpr (hc.trans_le ht.2)⟩
  · exact ⟨fun hc => ht.2.trans_lt ((hz c).2.mp hc),
      fun hc => (hy c).2.mpr (ht.1.trans_lt hc)⟩

/-- Root/zero equivalence on every refined position class follows from actual
root membership and the proved refined-cut signs. -/
theorem RefinedCuts.zero_iff {C D : Finset ℝ} {e : C ≃o D} {P Q : ℝ[X]}
    (r : RefinedCuts e P Q) (hP : P ≠ 0) (hQ : Q ≠ 0)
    {x y : ℝ} (h : Position r.cuts x y) : P.eval x = 0 ↔ Q.eval y = 0 := by
  classical
  constructor
  · intro hx
    have hxc : x ∈ C ∪ P.roots.toFinset := Finset.mem_union_right _
      (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr hx))
    have hy := h.eq_of_eq_cut ⟨x,hxc⟩ rfl
    rw [hy]
    exact (r.signs ⟨x,hxc⟩).1.mp hx
  · intro hy
    have hyc : y ∈ D ∪ Q.roots.toFinset := Finset.mem_union_right _
      (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQ).mpr hy))
    have hx := h.symm.eq_of_eq_cut ⟨y,hyc⟩ rfl
    rw [hx]
    apply (r.signs (r.cuts.symm ⟨y,hyc⟩)).1.mpr
    simpa only [r.cuts.apply_symm_apply] using hy

/-- Monotonicity on an entire position cell follows from its actual derivative sign. -/
theorem strictMonoOn_position {C D : Finset ℝ} (e : C ≃o D) (P : ℝ[X]) (x : ℝ)
    (hpos : ∀ z, Position e x z → 0 < P.derivative.eval z) :
    StrictMonoOn P.eval {z | Position e x z} := by
  apply strictMonoOn_of_deriv_pos (position_ordConnected e x).convex P.continuous.continuousOn
  intro z hz
  simpa only [Polynomial.deriv] using hpos z (interior_subset hz)

/-- The assembled refined cuts determine all the new point/gap signs. Root-free
old cells use IVT sign constancy; cells containing a new root use derivative
monotonicity and its transported order. -/
theorem RefinedCuts.signs_on_positions {C D : Finset ℝ} {e : C ≃o D} {P Q : ℝ[X]}
    (r : RefinedCuts e P Q) (hP : P.derivative ≠ 0) (hQ : Q.derivative ≠ 0)
    (hPC : ∀ z ∈ P.derivative.roots.toFinset, z ∈ C)
    (hderiv : ∀ x y, Position e x y → SameSign (P.derivative.eval x) (Q.derivative.eval y))
    (hforward : ∀ x, ∃ y, Position e x y ∧ SameSign (P.eval x) (Q.eval y))
    {x y : ℝ} (hxy : Position r.cuts x y) : SameSign (P.eval x) (Q.eval y) := by
  classical
  have hPn : P ≠ 0 := by intro h; subst P; simp at hP
  have hQn : Q ≠ 0 := by intro h; subst Q; simp at hQ
  have hbase := r.base_position hxy
  have hself : Position (OrderIso.refl C) x x := fun _ => ⟨Iff.rfl,Iff.rfl⟩
  by_cases hxC : x ∈ C
  · let c : ↥(C ∪ P.roots.toFinset) := ⟨x,Finset.mem_union_left _ hxC⟩
    have hy := hxy.eq_of_eq_cut c rfl
    simpa only [hy] using r.signs c
  · have hdx : P.derivative.eval x ≠ 0 := by
      intro hz
      exact hxC (hPC x (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr hz)))
    have hconst : ∀ z, Position (OrderIso.refl C) x z →
        SameSign (P.derivative.eval x) (P.derivative.eval z) := by
      intro z hz
      apply same_position_signs_of_roots_subset C [P.derivative] _ hz P.derivative (by simp)
      intro a ha
      apply hPC a
      simpa [rootCuts] using ha
    by_cases hroot : ∃ z, Position e x z ∧ Q.eval z = 0
    · obtain ⟨z,hz,hQz⟩ := hroot
      have hzm : z ∈ D ∪ Q.roots.toFinset := Finset.mem_union_right _
        (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hQn).mpr hQz))
      let c := r.cuts.symm ⟨z,hzm⟩
      have hPz : P.eval (c : ℝ) = 0 := (r.signs c).1.mpr (by
        simpa only [c,r.cuts.apply_symm_apply] using hQz)
      have hcz : Position e c z := by
        simpa only [c,r.cuts.apply_symm_apply] using r.positions c
      have hsource : Position (OrderIso.refl C) x c := by
        intro d
        exact ⟨(hz d).1.trans (hcz d).1.symm,(hz d).2.trans (hcz d).2.symm⟩
      have horder : ((c : ℝ) < x ↔ z < y) := by
        simpa only [c,r.cuts.apply_symm_apply] using (hxy c).1
      have hzero := r.zero_iff hPn hQn hxy
      rcases lt_or_gt_of_ne hdx with hn | hp
      · have hmP := strictMonoOn_position (OrderIso.refl C) (-P) x (by
          intro a ha
          simpa only [derivative_neg,eval_neg,neg_pos] using (hconst a ha).neg_iff.mp hn)
        have hmQ := strictMonoOn_position e (-Q) x (by
          intro a ha
          simpa only [derivative_neg,eval_neg,neg_pos] using (hderiv x a ha).neg_iff.mp hn)
        have hleft : 0 < -P.eval x ↔ (c : ℝ) < x := by
          simpa only [Polynomial.eval_neg,hPz,neg_zero] using hmP.lt_iff_lt hsource hself
        have hright : 0 < -Q.eval y ↔ z < y := by
          simpa only [Polynomial.eval_neg,hQz,neg_zero] using hmQ.lt_iff_lt hz hbase
        have hneg : SameSign (-P.eval x) (-Q.eval y) :=
          ⟨by simpa only [neg_eq_zero] using hzero,hleft.trans (horder.trans hright.symm)⟩
        simpa only [neg_neg] using hneg.neg
      · have hmP := strictMonoOn_position (OrderIso.refl C) P x
          (fun a ha => (hconst a ha).2.mp hp)
        have hmQ := strictMonoOn_position e Q x (fun a ha => (hderiv x a ha).2.mp hp)
        have hleft : 0 < P.eval x ↔ (c : ℝ) < x := by
          simpa only [hPz] using hmP.lt_iff_lt hsource hself
        have hright : 0 < Q.eval y ↔ z < y := by
          simpa only [hQz] using hmQ.lt_iff_lt hz hbase
        exact ⟨hzero,hleft.trans (horder.trans hright.symm)⟩
    · obtain ⟨z,hz,hs⟩ := hforward x
      have hnon : ∀ a ∈ {a | Position e x a}, Q.eval a ≠ 0 := by
        intro a ha hzero
        exact hroot ⟨a,ha,hzero⟩
      exact hs.trans (sameSign_of_no_roots Q _ (position_ordConnected e x).isPreconnected hnon hz hbase)

/-- Add one higher-degree polynomial to an entire ordered family sign table.
All root order and point/gap signs are proved, then the actual root set is restored. -/
def addPolynomialTable (ps qs : List ℝ[X]) (t : SignTableEquivalence ps qs) (P Q : ℝ[X])
    (hP : P.derivative ≠ 0) (hQ : Q.derivative ≠ 0)
    (hPC : ∀ r ∈ P.derivative.roots.toFinset, r ∈ rootCuts ps)
    (hQD : ∀ r ∈ Q.derivative.roots.toFinset, r ∈ rootCuts qs)
    (hderiv : ∀ x y, Position t.cuts x y → SameSign (P.derivative.eval x) (Q.derivative.eval y))
    (hpoints : ∀ c : rootCuts ps, SameSign (P.eval c) (Q.eval (t.cuts c)))
    (hlead : SameSign P.leadingCoeff Q.leadingCoeff)
    (hreflect : SameSign (P.comp (-X)).leadingCoeff (Q.comp (-X)).leadingCoeff)
    (hzero : List.Forall₂ (fun S T => (S = 0 ↔ T = 0)) ps qs) :
    SignTableEquivalence (P :: ps) (Q :: qs) := by
  let r := polynomialRefinement t.cuts P Q hP hQ hPC hQD hderiv hpoints hlead hreflect
  have hforward := polynomial_position_transfer t.cuts P Q hP hPC hderiv hpoints hlead hreflect
  have hPn : P ≠ 0 := by intro h; subst P; simp at hP
  have hQn : Q ≠ 0 := by intro h; subst Q; simp at hQ
  apply pruneSignTable (P :: ps) (Q :: qs) (rootCuts ps ∪ P.roots.toFinset)
    (rootCuts qs ∪ Q.roots.toFinset) r.cuts
  · rw [rootCuts_cons,Finset.union_comm]
  · rw [rootCuts_cons,Finset.union_comm]
  · exact List.Forall₂.cons (iff_of_false hPn hQn) hzero
  · intro x y hxy
    exact List.Forall₂.cons (r.signs_on_positions hP hQ hPC hderiv hforward hxy)
      (t.signs x y (r.base_position hxy))

#print axioms addPolynomialTable
#print axioms RefinedCuts.signs_on_positions
#print axioms polynomialRefinement
#print axioms RefinedCuts.base_position
#print axioms RefinedCuts.zero_iff
end LinearStochastic.RealQETableRefinement
