import LinearStochastic.RealQESignCells
import LinearStochastic.RealQEFiniteCells
import LinearStochastic.RealQERecursiveProjection

/-!
# Combining lower-degree signs into higher-degree cells

These are semantic induction steps, not an assumed sign-table oracle. Boundary
signs are proved from actual pseudo-remainders, and bounded open-cell signs are
reconstructed from the derivative and endpoint signs. The global projected
sign-table theorem still needs the ordering and unbounded-cell assembly.
-/
noncomputable section
namespace LinearStochastic.RealQECellComposition
open Polynomial Set RealQESignCells RealQEFiniteCells RealQEProjection RealQERecursiveProjection

/-- An increasing polynomial attains a positive value in a bounded open cell
exactly when its right endpoint value is positive. -/
theorem increasing_cell_positive_iff (P : ℝ[X]) (a b : ℝ) (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, 0 < P.derivative.eval x) :
    (∃ x ∈ Ioo a b, 0 < P.eval x) ↔ 0 < P.eval b := by
  constructor
  · rintro ⟨x,hx,hp⟩
    exact hp.trans ((strictMonoOn_cell P a b hd) ⟨hx.1.le,hx.2.le⟩
      (right_mem_Icc.mpr hab.le) hx.2)
  · intro hb
    rcases increasing_cell_trichotomy P a b hab hd with h | h | h
    · obtain ⟨x,hax,hxb⟩ := exists_between hab
      exact ⟨x,⟨hax,hxb⟩,h.2 x ⟨hax,hxb⟩⟩
    · exact False.elim (not_lt_of_ge h.1 hb)
    · obtain ⟨_,_,r,hr,_,_,hright,_⟩ := h
      obtain ⟨x,hrx,hxb⟩ := exists_between hr.2
      exact ⟨x,⟨hr.1.trans hrx,hxb⟩,hright x ⟨hrx,hxb⟩⟩

/-- The analogous negative-value test uses the left endpoint. -/
theorem increasing_cell_negative_iff (P : ℝ[X]) (a b : ℝ) (hab : a < b)
    (hd : ∀ x ∈ Ioo a b, 0 < P.derivative.eval x) :
    (∃ x ∈ Ioo a b, P.eval x < 0) ↔ P.eval a < 0 := by
  constructor
  · rintro ⟨x,hx,hn⟩
    exact ((strictMonoOn_cell P a b hd) (left_mem_Icc.mpr hab.le)
      ⟨hx.1.le,hx.2.le⟩ hx.1).trans hn
  · intro ha
    rcases increasing_cell_trichotomy P a b hab hd with h | h | h
    · exact False.elim (not_lt_of_ge h.1 ha)
    · obtain ⟨x,hax,hxb⟩ := exists_between hab
      exact ⟨x,⟨hax,hxb⟩,h.2 x ⟨hax,hxb⟩⟩
    · obtain ⟨_,_,r,hr,_,hleft,_,_⟩ := h
      obtain ⟨x,hax,hxr⟩ := exists_between hr.1
      exact ⟨x,⟨hax,hxr.trans hr.2⟩,hleft x ⟨hax,hxr⟩⟩

/-- Two increasing cells with matching endpoint signs realize exactly the same
three signs. This is the bounded-cell high-degree reconstruction step. -/
theorem increasing_cells_transfer (P Q : ℝ[X]) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d)
    (hP : ∀ x ∈ Ioo a b, 0 < P.derivative.eval x)
    (hQ : ∀ y ∈ Ioo c d, 0 < Q.derivative.eval y)
    (hac : SameSign (P.eval a) (Q.eval c)) (hbd : SameSign (P.eval b) (Q.eval d)) :
    ∀ x ∈ Ioo a b, ∃ y ∈ Ioo c d, SameSign (P.eval x) (Q.eval y) := by
  intro x hx
  rcases lt_trichotomy (P.eval x) 0 with hn | hz | hp
  · have ha := (increasing_cell_negative_iff P a b hab hP).mp ⟨x,hx,hn⟩
    obtain ⟨y,hy,hyn⟩ := (increasing_cell_negative_iff Q c d hcd hQ).mpr (hac.neg_iff.mp ha)
    exact ⟨y,hy,⟨by simp [ne_of_lt hn,ne_of_lt hyn],by simp [not_lt_of_gt hn,not_lt_of_gt hyn]⟩⟩
  · have hm := strictMonoOn_cell P a b hP
    have ha : P.eval a < 0 := by
      simpa only [hz] using hm (left_mem_Icc.mpr hab.le) ⟨hx.1.le,hx.2.le⟩ hx.1
    have hb : 0 < P.eval b := by
      simpa only [hz] using hm ⟨hx.1.le,hx.2.le⟩ (right_mem_Icc.mpr hab.le) hx.2
    obtain ⟨y,⟨hy,hyz⟩,_⟩ := (increasing_cell_root_iff Q c d hcd hQ).mpr
      ⟨hac.neg_iff.mp ha,hbd.2.mp hb⟩
    exact ⟨y,hy,by simp only [hz,hyz]; exact SameSign.refl 0⟩
  · have hb := (increasing_cell_positive_iff P a b hab hP).mp ⟨x,hx,hp⟩
    obtain ⟨y,hy,hyp⟩ := (increasing_cell_positive_iff Q c d hcd hQ).mpr (hbd.2.mp hb)
    exact ⟨y,hy,⟨by simp [ne_of_gt hp,ne_of_gt hyp],by simp [hp,hyp]⟩⟩

/-- Matching lower-degree signs which are constant on each open cell can be
extended by the higher-degree dividend. No sampled point is assumed to exist. -/
theorem bounded_cell_extension (P Q : ℝ[X]) (ps qs : List ℝ[X])
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hP : ∀ x ∈ Ioo a b, 0 < P.derivative.eval x)
    (hQ : ∀ y ∈ Ioo c d, 0 < Q.derivative.eval y)
    (hac : SameSign (P.eval a) (Q.eval c)) (hbd : SameSign (P.eval b) (Q.eval d))
    (hbase : ∀ x ∈ Ioo a b, ∀ y ∈ Ioo c d,
      List.Forall₂ (fun S T => SameSign (S.eval x) (T.eval y)) ps qs) :
    ∀ x ∈ Ioo a b, ∃ y ∈ Ioo c d,
      List.Forall₂ (fun S T => SameSign (S.eval x) (T.eval y)) (P :: ps) (Q :: qs) := by
  intro x hx
  obtain ⟨y,hy,hs⟩ := increasing_cells_transfer P Q a b c d hab hcd hP hQ hac hbd x hx
  exact ⟨y,hy,List.Forall₂.cons hs (hbase x hx y hy)⟩

/-- Negative derivative cells follow from the already proved increasing case. -/
theorem decreasing_cells_transfer (P Q : ℝ[X]) (a b c d : ℝ)
    (hab : a < b) (hcd : c < d)
    (hP : ∀ x ∈ Ioo a b, P.derivative.eval x < 0)
    (hQ : ∀ y ∈ Ioo c d, Q.derivative.eval y < 0)
    (hac : SameSign (P.eval a) (Q.eval c)) (hbd : SameSign (P.eval b) (Q.eval d)) :
    ∀ x ∈ Ioo a b, ∃ y ∈ Ioo c d, SameSign (P.eval x) (Q.eval y) := by
  intro x hx
  obtain ⟨y,hy,hs⟩ := increasing_cells_transfer (-P) (-Q) a b c d hab hcd
    (by simpa only [derivative_neg,eval_neg,neg_pos] using hP)
    (by simpa only [derivative_neg,eval_neg,neg_pos] using hQ)
    (by simpa only [eval_neg] using hac.neg)
    (by simpa only [eval_neg] using hbd.neg) x hx
  exact ⟨y,hy,by simpa only [eval_neg,neg_neg] using hs.neg⟩

/-- Full three-sign behavior at positive infinity, including the zero polynomial. -/
theorem eventually_sign_leading (P : ℝ[X]) :
    ∀ᶠ x in Filter.atTop, SameSign (P.eval x) P.leadingCoeff := by
  filter_upwards [positive_infinity_signs P] with x hx
  exact ⟨hx.1.trans Polynomial.leadingCoeff_eq_zero.symm,hx.2⟩

theorem reflected_leading_signs (P Q : ℝ[X]) (hdegree : P.natDegree = Q.natDegree)
    (hlead : SameSign P.leadingCoeff Q.leadingCoeff) :
    SameSign (P.comp (-X)).leadingCoeff (Q.comp (-X)).leadingCoeff := by
  rw [Polynomial.leadingCoeff_comp (by simp : (-X : ℝ[X]).natDegree ≠ 0),
    Polynomial.leadingCoeff_comp (by simp : (-X : ℝ[X]).natDegree ≠ 0)]
  simpa only [hdegree,mul_comm] using hlead.mul_left ((-X : ℝ[X]).leadingCoeff ^ Q.natDegree)

/-- A right ray is reduced to a proved bounded-cell transfer by taking actual
far-right endpoints whose signs are determined by the leading coefficients. -/
theorem increasing_right_cells_transfer (P Q : ℝ[X]) (a c : ℝ)
    (hP : ∀ x, a < x → 0 < P.derivative.eval x)
    (hQ : ∀ y, c < y → 0 < Q.derivative.eval y)
    (hac : SameSign (P.eval a) (Q.eval c))
    (hlead : SameSign P.leadingCoeff Q.leadingCoeff) :
    ∀ x, a < x → ∃ y, c < y ∧ SameSign (P.eval x) (Q.eval y) := by
  intro x hx
  obtain ⟨b,hb,hxb⟩ := (Filter.Eventually.and (eventually_sign_leading P)
    (Filter.eventually_gt_atTop x)).exists
  obtain ⟨d,hd,hcd⟩ := (Filter.Eventually.and (eventually_sign_leading Q)
    (Filter.eventually_gt_atTop c)).exists
  have hbd := hb.trans (hlead.trans hd.symm)
  obtain ⟨y,hy,hs⟩ := increasing_cells_transfer P Q a b c d (hx.trans hxb) hcd
    (fun t ht => hP t ht.1) (fun t ht => hQ t ht.1) hac hbd x ⟨hx,hxb⟩
  exact ⟨y,hy.1,hs⟩

/-- Matching reflected leading coefficients supply the corresponding negative
infinity signs, completing the left-ray reconstruction. -/
theorem increasing_left_cells_transfer (P Q : ℝ[X]) (b d : ℝ)
    (hP : ∀ x, x < b → 0 < P.derivative.eval x)
    (hQ : ∀ y, y < d → 0 < Q.derivative.eval y)
    (hbd : SameSign (P.eval b) (Q.eval d))
    (hlead : SameSign (P.comp (-X)).leadingCoeff (Q.comp (-X)).leadingCoeff) :
    ∀ x, x < b → ∃ y, y < d ∧ SameSign (P.eval x) (Q.eval y) := by
  intro x hx
  obtain ⟨u,hu,hux⟩ := (Filter.Eventually.and (eventually_sign_leading (P.comp (-X)))
    (Filter.eventually_gt_atTop (-x))).exists
  obtain ⟨v,hv,hvd⟩ := (Filter.Eventually.and (eventually_sign_leading (Q.comp (-X)))
    (Filter.eventually_gt_atTop (-d))).exists
  have hac : SameSign (P.eval (-u)) (Q.eval (-v)) := by
    simpa only [eval_comp,eval_neg,eval_X] using hu.trans (hlead.trans hv.symm)
  obtain ⟨y,hy,hs⟩ := increasing_cells_transfer P Q (-u) b (-v) d
    (by linarith) (by linarith) (fun t ht => hP t ht.2) (fun t ht => hQ t ht.2)
    hac hbd x ⟨by linarith,hx⟩
  exact ⟨y,hy.2,hs⟩

/-- With no finite boundary cuts, both infinity signs produce a bounded window
and hence the whole-line higher-degree transfer. -/
theorem increasing_line_transfer (P Q : ℝ[X])
    (hP : ∀ x, 0 < P.derivative.eval x) (hQ : ∀ y, 0 < Q.derivative.eval y)
    (hlead : SameSign P.leadingCoeff Q.leadingCoeff)
    (hreflect : SameSign (P.comp (-X)).leadingCoeff (Q.comp (-X)).leadingCoeff) :
    ∀ x, ∃ y, SameSign (P.eval x) (Q.eval y) := by
  intro x
  obtain ⟨u,hu,hux⟩ := (Filter.Eventually.and (eventually_sign_leading (P.comp (-X)))
    (Filter.eventually_gt_atTop (-x))).exists
  obtain ⟨v,hv⟩ := (eventually_sign_leading (Q.comp (-X))).exists
  have hac : SameSign (P.eval (-u)) (Q.eval (-v)) := by
    simpa only [eval_comp,eval_neg,eval_X] using hu.trans (hreflect.trans hv.symm)
  obtain ⟨y,_,hs⟩ := increasing_right_cells_transfer P Q (-u) (-v)
    (fun t _ => hP t) (fun t _ => hQ t) hac hlead x (by linarith)
  exact ⟨y,hs⟩

section Parameters
variable {R : Type*} [CommRing R]

/-- Agreement on the concrete finite projection family forces agreement of every
input coefficient, including coefficients exposed by parameter degree drops. -/
theorem projected_coeff_signs (qs : List R[X]) (f g : R →+* ℝ)
    (hproject : ∀ c ∈ projectionCoefficients qs, SameSign (f c) (g c))
    (P : R[X]) (hP : P ∈ qs) (k : ℕ) :
    SameSign (f (P.coeff k)) (g (P.coeff k)) := by
  by_cases hz : P.coeff k = 0
  · simpa only [hz,map_zero] using SameSign.refl 0
  · exact hproject _ (coeff_mem_projectionCoefficients qs P hP k hz)

/-- Equal finite projected signs force equal specialized supports, hence equal
actual degrees even when symbolic leading coefficients disappear. -/
theorem projected_support_eq (qs : List R[X]) (f g : R →+* ℝ)
    (hproject : ∀ c ∈ projectionCoefficients qs, SameSign (f c) (g c))
    (P : R[X]) (hP : P ∈ qs) : (P.map f).support = (P.map g).support := by
  ext k
  simp only [Polynomial.mem_support_iff,Polynomial.coeff_map]
  exact not_congr (projected_coeff_signs qs f g hproject P hP k).1

theorem projected_natDegree_eq (qs : List R[X]) (f g : R →+* ℝ)
    (hproject : ∀ c ∈ projectionCoefficients qs, SameSign (f c) (g c))
    (P : R[X]) (hP : P ∈ qs) : (P.map f).natDegree = (P.map g).natDegree := by
  simp only [Polynomial.natDegree,Polynomial.degree,projected_support_eq qs f g hproject P hP]

theorem projected_leading_signs (qs : List R[X]) (f g : R →+* ℝ)
    (hproject : ∀ c ∈ projectionCoefficients qs, SameSign (f c) (g c))
    (P : R[X]) (hP : P ∈ qs) : SameSign (P.map f).leadingCoeff (P.map g).leadingCoeff := by
  simp only [Polynomial.leadingCoeff,Polynomial.coeff_map,
    projected_natDegree_eq qs f g hproject P hP]
  exact projected_coeff_signs qs f g hproject P hP _

/-- Degree drops of a boundary polynomial are resolved inside the actual recursive
family before the pseudo-remainder identity is applied in either specialization. -/
theorem boundary_signs_transfer (P : R[X]) (qs : List R[X]) (f g : R →+* ℝ) (a b : ℝ)
    (hvalues : ∀ S ∈ lowerFamily P qs, SameSign (S.eval₂ f a) (S.eval₂ g b))
    (hleads : ∀ S ∈ lowerFamily P qs, SameSign (f S.leadingCoeff) (g S.leadingCoeff))
    (hroot : ∃ Q ∈ lowerFamily P qs, Q.map f ≠ 0 ∧ Q.eval₂ f a = 0) :
    SameSign (P.eval₂ f a) (P.eval₂ g b) := by
  obtain ⟨Q,hQ,hQne,hQa⟩ := hroot
  obtain ⟨S,hS,hmap,hSf⟩ := branchClosure_specialization P Q f hQne
  have hSm := lowerFamily_branchClosure P Q qs hQ S hS
  have hSa : S.eval₂ f a = 0 := by
    have h := congrArg (Polynomial.eval a) hmap
    simpa only [Polynomial.eval_map,hQa] using h
  have hSb : S.eval₂ g b = 0 := (hvalues S hSm).1.mp hSa
  have hSg : g S.leadingCoeff ≠ 0 := by
    intro hzero
    exact hSf ((hleads S hSm).1.mpr hzero)
  have hdeg : S.natDegree ≠ 0 := by
    intro hd
    have hc : S = C S.leadingCoeff := by
      simpa only [Polynomial.leadingCoeff,hd] using Polynomial.eq_C_of_natDegree_eq_zero hd
    have hv := congrArg (fun T : R[X] => T.eval₂ f a) hc
    have hzero : f S.leadingCoeff = 0 := by
      simpa only [Polynomial.eval₂_C,hSa] using hv.symm
    exact hSf hzero
  have hSne : S ≠ 0 := by intro h; simp [h] at hdeg
  have hrem := (lowerFamily_closed P qs S hSm hdeg).1
  have hf : SameSign (P.eval₂ f a) ((remainder P S).eval₂ f a) :=
    remainder_signs P S hSne f a hSa hSf
  have hg : SameSign (P.eval₂ g b) ((remainder P S).eval₂ g b) :=
    remainder_signs P S hSne g b hSb hSg
  exact hf.trans ((hvalues _ hrem).trans hg.symm)

/-- The top-level zero-leading branch is already represented by the actual
lower-degree eraseLead member, so matching signs transfer without a degree assumption. -/
theorem zero_leading_branch_transfer (P : R[X]) (qs : List R[X]) (f g : R →+* ℝ) (a b : ℝ)
    (hf : f P.leadingCoeff = 0) (hg : g P.leadingCoeff = 0)
    (hvalues : ∀ S ∈ lowerFamily P qs, SameSign (S.eval₂ f a) (S.eval₂ g b)) :
    SameSign (P.eval₂ f a) (P.eval₂ g b) := by
  have h := hvalues P.eraseLead (eraseLead_mem_lowerFamily P qs)
  rwa [RealQEPseudoDivision.evaluate_eraseLead_of_leading_zero P f a hf,
    RealQEPseudoDivision.evaluate_eraseLead_of_leading_zero P g b hg] at h

end Parameters

#print axioms increasing_left_cells_transfer
#print axioms increasing_line_transfer
#print axioms projected_natDegree_eq
#print axioms projected_leading_signs
#print axioms boundary_signs_transfer
#print axioms zero_leading_branch_transfer
#print axioms increasing_cells_transfer
#print axioms bounded_cell_extension
end LinearStochastic.RealQECellComposition
