import LinearStochastic.RealQECutTransport
import LinearStochastic.RealQECellComposition

/-!
# Canonical intervals of a finite cut set

The nearest lower and upper cuts represent each open position class as an actual
bounded interval, ray, or the whole line. This connects finite ordered cut
transport with the proved polynomial cell-interpolation lemmas.
-/
noncomputable section
namespace LinearStochastic.RealQEGapIntervals
open Set Polynomial RealQEFiniteCells RealQECutTransport RealQECellComposition

/-- Optional nearest cuts. The specifications characterize every cut below or
above x, rather than assuming an unproved interval decomposition. -/
structure GapBounds (C : Finset ℝ) (x : ℝ) where
  left : Option C
  right : Option C
  left_spec : ∀ c : C, (c : ℝ) < x ↔ match left with
    | none => False
    | some a => c ≤ a
  right_spec : ∀ c : C, x < (c : ℝ) ↔ match right with
    | none => False
    | some b => b ≤ c

/-- The bounds are constructed from maxima/minima of finite subsets. -/
def gapBounds (C : Finset ℝ) (x : ℝ) : GapBounds C x := by
  classical
  let lo : Finset C := C.attach.filter (fun c : C => (c : ℝ) < x)
  let hi : Finset C := C.attach.filter (fun c : C => x < (c : ℝ))
  have hleft : ∃ a : Option C, ∀ c : C, (c : ℝ) < x ↔ match a with
      | none => False | some a => c ≤ a := by
    by_cases hlo : lo.Nonempty
    · refine ⟨some (lo.max' hlo),?_⟩
      intro c
      constructor
      · intro hc
        exact Finset.le_max' lo c (Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,hc⟩)
      · intro hc
        exact (show (c : ℝ) ≤ (lo.max' hlo : ℝ) from hc).trans_lt
          (Finset.mem_filter.mp (Finset.max'_mem lo hlo)).2
    · refine ⟨none,?_⟩
      intro c
      constructor
      · intro hc
        exact hlo ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,hc⟩⟩
      · exact False.elim
  have hright : ∃ b : Option C, ∀ c : C, x < (c : ℝ) ↔ match b with
      | none => False | some b => b ≤ c := by
    by_cases hhi : hi.Nonempty
    · refine ⟨some (hi.min' hhi),?_⟩
      intro c
      constructor
      · intro hc
        exact Finset.min'_le hi c (Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,hc⟩)
      · intro hc
        exact (Finset.mem_filter.mp (Finset.min'_mem hi hhi)).2.trans_le hc
    · refine ⟨none,?_⟩
      intro c
      constructor
      · intro hc
        exact hhi ⟨c,Finset.mem_filter.mpr ⟨Finset.mem_attach _ _,hc⟩⟩
      · exact False.elim
  exact ⟨Classical.choose hleft,Classical.choose hright,
    Classical.choose_spec hleft,Classical.choose_spec hright⟩

/-- The same nearest-cut description works in every corresponding target cut set. -/
theorem position_iff_bounds {C D : Finset ℝ} (e : C ≃o D) (x : ℝ) (hx : x ∉ C)
    (b : GapBounds C x) (y : ℝ) :
    Position e x y ↔
      (match b.left with | none => True | some a => (e a : ℝ) < y) ∧
      (match b.right with | none => True | some c => y < (e c : ℝ)) := by
  constructor
  · intro h
    constructor
    · cases hl : b.left with
      | none => trivial
      | some a => exact (h a).1.mp ((b.left_spec a).mpr (by simp only [hl]; exact le_rfl))
    · cases hr : b.right with
      | none => trivial
      | some c => exact (h c).2.mp ((b.right_spec c).mpr (by simp only [hr]; exact le_rfl))
  · rintro ⟨hl,hr⟩ c
    rcases lt_trichotomy (c : ℝ) x with hc | hc | hc
    · have hleft := (b.left_spec c).mp hc
      have htarget : (e c : ℝ) < y := by
        cases hla : b.left with
        | none => simp only [hla] at hleft
        | some a =>
          have hca : c ≤ a := by simpa only [hla] using hleft
          have hay : (e a : ℝ) < y := by simpa only [hla] using hl
          exact (show (e c : ℝ) ≤ (e a : ℝ) from e.monotone hca).trans_lt hay
      exact ⟨iff_of_true hc htarget,iff_of_false (not_lt_of_gt hc) (not_lt_of_gt htarget)⟩
    · exact False.elim (hx (hc ▸ c.2))
    · have hright := (b.right_spec c).mp hc
      have htarget : y < (e c : ℝ) := by
        cases hrb : b.right with
        | none => simp only [hrb] at hright
        | some a =>
          have hac : a ≤ c := by simpa only [hrb] using hright
          have hya : y < (e a : ℝ) := by simpa only [hrb] using hr
          exact hya.trans_le (e.monotone hac)
      exact ⟨iff_of_false (not_lt_of_gt hc) (not_lt_of_gt htarget),iff_of_true hc htarget⟩

/-- Complete increasing-cell transfer, stated directly in terms of ordered cuts.
The four bounded/unbounded cases are obtained from the constructed finite bounds. -/
theorem increasing_position_transfer {C D : Finset ℝ} (e : C ≃o D)
    (P Q : ℝ[X]) (x : ℝ) (hx : x ∉ C)
    (hP : ∀ z, Position (OrderIso.refl C) x z → 0 < P.derivative.eval z)
    (hQ : ∀ y, Position e x y → 0 < Q.derivative.eval y)
    (hpoints : ∀ c : C, SameSign (P.eval c) (Q.eval (e c)))
    (hlead : SameSign P.leadingCoeff Q.leadingCoeff)
    (hreflect : SameSign (P.comp (-X)).leadingCoeff (Q.comp (-X)).leadingCoeff) :
    ∃ y, Position e x y ∧ SameSign (P.eval x) (Q.eval y) := by
  let b := gapBounds C x
  have hsource := position_iff_bounds (OrderIso.refl C) x hx b
  have htarget := position_iff_bounds e x hx b
  have hself : Position (OrderIso.refl C) x x := fun _ => ⟨Iff.rfl,Iff.rfl⟩
  have hxb := (hsource x).mp hself
  cases hl : b.left with
  | none =>
    cases hr : b.right with
    | none =>
      obtain ⟨y,hy⟩ := increasing_line_transfer P Q
        (fun z => hP z ((hsource z).mpr (by simp [hl,hr])))
        (fun y => hQ y ((htarget y).mpr (by simp [hl,hr]))) hlead hreflect x
      exact ⟨y,(htarget y).mpr (by simp [hl,hr]),hy⟩
    | some c =>
      have hxc : x < (c : ℝ) := by simpa only [hl,hr,true_and,OrderIso.refl_apply] using hxb
      obtain ⟨y,hy,hs⟩ := increasing_left_cells_transfer P Q c (e c)
        (fun z hz => hP z ((hsource z).mpr (by simpa only [hl,hr,true_and,OrderIso.refl_apply] using hz)))
        (fun y hy => hQ y ((htarget y).mpr (by simpa only [hl,hr,true_and] using hy)))
        (hpoints c) hreflect x hxc
      exact ⟨y,(htarget y).mpr (by simpa only [hl,hr,true_and] using hy),hs⟩
  | some a =>
    cases hr : b.right with
    | none =>
      have hax : (a : ℝ) < x := by simpa only [hl,hr,and_true,OrderIso.refl_apply] using hxb
      obtain ⟨y,hy,hs⟩ := increasing_right_cells_transfer P Q a (e a)
        (fun z hz => hP z ((hsource z).mpr (by simpa only [hl,hr,and_true,OrderIso.refl_apply] using hz)))
        (fun y hy => hQ y ((htarget y).mpr (by simpa only [hl,hr,and_true] using hy)))
        (hpoints a) hlead x hax
      exact ⟨y,(htarget y).mpr (by simpa only [hl,hr,and_true] using hy),hs⟩
    | some c =>
      have haxc : (a : ℝ) < x ∧ x < (c : ℝ) := by
        simpa only [hl,hr,OrderIso.refl_apply] using hxb
      have hac : (a : ℝ) < c := haxc.1.trans haxc.2
      obtain ⟨y,hy,hs⟩ := increasing_cells_transfer P Q a c (e a) (e c) hac (e.strictMono hac)
        (fun z hz => hP z ((hsource z).mpr (by simpa only [hl,hr,OrderIso.refl_apply,Set.mem_Ioo] using hz)))
        (fun y hy => hQ y ((htarget y).mpr (by simpa only [hl,hr,Set.mem_Ioo] using hy)))
        (hpoints a) (hpoints c) x haxc
      exact ⟨y,(htarget y).mpr (by simpa only [hl,hr,Set.mem_Ioo] using hy),hs⟩

/-- Extra cuts do not destroy the constant-sign property of the true root cells. -/
theorem same_position_signs_of_roots_subset (C : Finset ℝ) (qs : List ℝ[X])
    (hcuts : rootCuts qs ⊆ C) {x y : ℝ} (h : Position (OrderIso.refl C) x y) :
    ∀ P ∈ qs, SameSign (P.eval x) (P.eval y) := by
  apply same_position_signs qs
  intro c
  exact h ⟨c,hcuts c.2⟩

/-- Complete local witness reconstruction from only lower-degree derivative
signs, actual cut-point values, and the two leading-coefficient infinity signs. -/
theorem polynomial_position_transfer {C D : Finset ℝ} (e : C ≃o D) (P Q : ℝ[X])
    (hPderiv : P.derivative ≠ 0)
    (hPcuts : ∀ r ∈ P.derivative.roots.toFinset, r ∈ C)
    (hderiv : ∀ x y, Position e x y → SameSign (P.derivative.eval x) (Q.derivative.eval y))
    (hpoints : ∀ c : C, SameSign (P.eval c) (Q.eval (e c)))
    (hlead : SameSign P.leadingCoeff Q.leadingCoeff)
    (hreflect : SameSign (P.comp (-X)).leadingCoeff (Q.comp (-X)).leadingCoeff) :
    ∀ x, ∃ y, Position e x y ∧ SameSign (P.eval x) (Q.eval y) := by
  intro x
  by_cases hx : x ∈ C
  · exact ⟨e ⟨x,hx⟩,Position.point e ⟨x,hx⟩,hpoints ⟨x,hx⟩⟩
  · have hne : P.derivative.eval x ≠ 0 := by
      intro hz
      apply hx
      apply hPcuts x
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hPderiv).mpr hz)
    have hconst : ∀ z, Position (OrderIso.refl C) x z →
        SameSign (P.derivative.eval x) (P.derivative.eval z) := by
      intro z hz
      apply same_position_signs_of_roots_subset C [P.derivative] _ hz P.derivative (by simp)
      intro r hr
      apply hPcuts r
      simpa [rootCuts] using hr
    rcases lt_or_gt_of_ne hne with hn | hp
    · obtain ⟨y,hy,hs⟩ := increasing_position_transfer e (-P) (-Q) x hx
        (by intro z hz; simpa only [Polynomial.derivative_neg,Polynomial.eval_neg,neg_pos]
            using (hconst z hz).neg_iff.mp hn)
        (by intro y hy; simpa only [Polynomial.derivative_neg,Polynomial.eval_neg,neg_pos]
            using (hderiv x y hy).neg_iff.mp hn)
        (by intro c; simpa only [Polynomial.eval_neg] using (hpoints c).neg)
        (by simpa only [Polynomial.leadingCoeff_neg] using hlead.neg)
        (by simpa only [Polynomial.neg_comp,Polynomial.leadingCoeff_neg] using hreflect.neg)
      exact ⟨y,hy,by simpa only [Polynomial.eval_neg,neg_neg] using hs.neg⟩
    · exact increasing_position_transfer e P Q x hx
        (fun z hz => (hconst z hz).2.mp hp)
        (fun y hy => (hderiv x y hy).2.mp hp) hpoints hlead hreflect

#print axioms polynomial_position_transfer
#print axioms gapBounds
#print axioms position_iff_bounds
#print axioms increasing_position_transfer
end LinearStochastic.RealQEGapIntervals
