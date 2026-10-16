import LinearStochastic.RealQETableRefinement

/-!
# Correctness of the symbolic coefficient projection

The induction invariant is an exact ordered root-cut sign table, including all
point and gap signs. This file applies the proved high-degree refinement step
to the genuinely terminating coefficient recursion.
-/
noncomputable section
namespace LinearStochastic.RealQEProjectionCorrectness
open Polynomial RealQEFiniteCells RealQECutTransport RealQEGapIntervals
open RealQETableRefinement RealQERecursiveProjection RealQECellComposition RealQEProjection
variable {R : Type*} [CommRing R]

abbrev FamilyTable (qs : List R[X]) (f g : R →+* ℝ) :=
  SignTableEquivalence (qs.map (Polynomial.map f)) (qs.map (Polynomial.map g))

theorem family_signs {qs : List R[X]} {f g : R →+* ℝ} (t : FamilyTable qs f g)
    (x y : ℝ) (h : Position t.cuts x y) :
    ∀ P ∈ qs, SameSign ((P.map f).eval x) ((P.map g).eval y) := by
  simpa only [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
    using t.signs x y h

theorem projected_zero_iff (qs : List R[X]) (f g : R →+* ℝ)
    (hproject : ∀ c ∈ projectionCoefficients qs, SameSign (f c) (g c))
    (P : R[X]) (hP : P ∈ qs) : P.map f = 0 ↔ P.map g = 0 := by
  have hs := projected_support_eq qs f g hproject P hP
  rw [← Polynomial.support_eq_empty,← Polynomial.support_eq_empty,hs]

/-- A subfamily or a family represented by identical specializations inherits
an exact ordered table after auxiliary roots are pruned. -/
def represented_table (ps qs : List R[X]) (f g : R →+* ℝ) (t : FamilyTable qs f g)
    (hrep : ∀ P ∈ ps, ∃ Q ∈ qs, P.map f = Q.map f ∧ P.map g = Q.map g)
    (hzero : ∀ P ∈ ps, P.map f = 0 ↔ P.map g = 0) : FamilyTable ps f g := by
  have hcoverf : rootCuts (ps.map (Polynomial.map f)) ⊆ rootCuts (qs.map (Polynomial.map f)) := by
    intro x hx
    obtain ⟨S,hS,hne,hroot⟩ := (mem_rootCuts _ x).mp hx
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hS
    obtain ⟨Q,hQ,hf,_⟩ := hrep P hP
    apply (mem_rootCuts _ x).mpr
    refine ⟨Q.map f,List.mem_map.mpr ⟨Q,hQ,rfl⟩,?_,?_⟩
    · rwa [← hf]
    · rwa [← hf]
  have hcoverg : rootCuts (ps.map (Polynomial.map g)) ⊆ rootCuts (qs.map (Polynomial.map g)) := by
    intro x hx
    obtain ⟨S,hS,hne,hroot⟩ := (mem_rootCuts _ x).mp hx
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hS
    obtain ⟨Q,hQ,_,hg⟩ := hrep P hP
    apply (mem_rootCuts _ x).mpr
    refine ⟨Q.map g,List.mem_map.mpr ⟨Q,hQ,rfl⟩,?_,?_⟩
    · rwa [← hg]
    · rwa [← hg]
  apply pruneSignTable _ _ _ _ t.cuts hcoverf hcoverg
  · simpa only [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same] using hzero
  · intro x y hxy
    simp only [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
    intro P hP
    obtain ⟨Q,hQ,hf,hg⟩ := hrep P hP
    rw [hf,hg]
    exact family_signs t x y hxy Q hQ

/-- Constant families have no real root cuts, including identically zero members. -/
theorem constant_family_roots_empty (qs : List R[X])
    (hconst : ∀ P ∈ qs, P.natDegree = 0) (f : R →+* ℝ) :
    rootCuts (qs.map (Polynomial.map f)) = ∅ := by
  classical
  induction qs with
  | nil => simp [rootCuts]
  | cons P qs ih =>
    have hc := Polynomial.eq_C_of_natDegree_eq_zero (hconst P (by simp))
    rw [List.map_cons,rootCuts_cons,hc,Polynomial.map_C]
    simp only [Polynomial.roots_C,Multiset.toFinset_zero,Finset.empty_union]
    exact ih (fun Q hQ => hconst Q (List.mem_cons_of_mem _ hQ))

/-- Base case of the actual projection recursion. -/
def constant_family_table (qs : List R[X]) (hconst : ∀ P ∈ qs, P.natDegree = 0)
    (f g : R →+* ℝ)
    (hcoef : ∀ c ∈ qs.map (fun P => P.coeff 0), SameSign (f c) (g c)) : FamilyTable qs f g := by
  letI : IsEmpty (rootCuts (qs.map (Polynomial.map f))) :=
    Finset.isEmpty_coe_sort.mpr (constant_family_roots_empty qs hconst f)
  letI : IsEmpty (rootCuts (qs.map (Polynomial.map g))) :=
    Finset.isEmpty_coe_sort.mpr (constant_family_roots_empty qs hconst g)
  refine ⟨OrderIso.ofIsEmpty _ _,?_⟩
  intro x y _
  simp only [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
  intro P hP
  have hc := Polynomial.eq_C_of_natDegree_eq_zero (hconst P hP)
  have hv := hcoef (P.coeff 0) (List.mem_map.mpr ⟨P,hP,rfl⟩)
  have hf := congrArg (fun T : R[X] => (T.map f).eval x) hc
  have hg := congrArg (fun T : R[X] => (T.map g).eval y) hc
  rw [Polynomial.map_C,Polynomial.eval_C] at hf hg
  rw [hf,hg]
  exact hv

/-- The high-degree semantic step for the actual symbolic lower family. All
boundary signs come from the proved pseudo-remainder construction. -/
def nonzero_family_extension (P : R[X]) (qs : List R[X]) (hp : P.natDegree ≠ 0)
    (f g : R →+* ℝ) (hf : f P.leadingCoeff ≠ 0) (hg : g P.leadingCoeff ≠ 0)
    (t : FamilyTable (lowerFamily P qs) f g)
    (hcoef : ∀ c ∈ projectionCoefficients (lowerFamily P qs), SameSign (f c) (g c))
    (hlead : SameSign (f P.leadingCoeff) (g P.leadingCoeff)) :
    FamilyTable (P :: lowerFamily P qs) f g := by
  have hnf := Polynomial.natDegree_map_of_leadingCoeff_ne_zero f hf
  have hng := Polynomial.natDegree_map_of_leadingCoeff_ne_zero g hg
  have hPf : (P.map f).derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (hnf ▸ hp)
  have hPg : (P.map g).derivative ≠ 0 := Polynomial.derivative_ne_zero.mpr (hng ▸ hp)
  have hderivmem := derivative_mem_lowerFamily P qs
  have hCf : ∀ r ∈ (P.map f).derivative.roots.toFinset,
      r ∈ rootCuts ((lowerFamily P qs).map (Polynomial.map f)) := by
    intro r hr
    rw [Polynomial.derivative_map] at hr
    have hroot := Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp hr)
    exact (mem_rootCuts _ r).mpr ⟨P.derivative.map f,List.mem_map.mpr ⟨_,hderivmem,rfl⟩,
      hroot.1,hroot.2⟩
  have hCg : ∀ r ∈ (P.map g).derivative.roots.toFinset,
      r ∈ rootCuts ((lowerFamily P qs).map (Polynomial.map g)) := by
    intro r hr
    rw [Polynomial.derivative_map] at hr
    have hroot := Polynomial.mem_roots'.mp (Multiset.mem_toFinset.mp hr)
    exact (mem_rootCuts _ r).mpr ⟨P.derivative.map g,List.mem_map.mpr ⟨_,hderivmem,rfl⟩,
      hroot.1,hroot.2⟩
  have hderiv : ∀ x y, Position t.cuts x y →
      SameSign ((P.map f).derivative.eval x) ((P.map g).derivative.eval y) := by
    intro x y hxy
    simpa only [Polynomial.derivative_map] using family_signs t x y hxy P.derivative hderivmem
  have hpoints : ∀ c : rootCuts ((lowerFamily P qs).map (Polynomial.map f)),
      SameSign ((P.map f).eval c) ((P.map g).eval (t.cuts c)) := by
    intro c
    have hvalues := family_signs t c (t.cuts c) (Position.point t.cuts c)
    have hleads : ∀ S ∈ lowerFamily P qs, SameSign (f S.leadingCoeff) (g S.leadingCoeff) :=
      fun S hS => hcoef _ (leadingCoeff_mem_projectionCoefficients _ S hS)
    obtain ⟨S,hS,hSn,hSr⟩ := (mem_rootCuts _ (c : ℝ)).mp c.2
    obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hS
    have hb := boundary_signs_transfer P qs f g c (t.cuts c)
      (by simpa only [Polynomial.eval_map] using hvalues) hleads
      ⟨Q,hQ,hSn,by simpa only [Polynomial.eval_map] using hSr⟩
    simpa only [Polynomial.eval_map] using hb
  have hl : SameSign (P.map f).leadingCoeff (P.map g).leadingCoeff := by
    rwa [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero f hf,
      Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero g hg]
  have hz : List.Forall₂ (fun S T => (S = 0 ↔ T = 0))
      ((lowerFamily P qs).map (Polynomial.map f)) ((lowerFamily P qs).map (Polynomial.map g)) := by
    simp only [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
    exact projected_zero_iff _ f g hcoef
  exact addPolynomialTable _ _ t (P.map f) (P.map g) hPf hPg hCf hCg hderiv hpoints hl
    (reflected_leading_signs _ _ (hnf.trans hng.symm) hl) hz

/-- The complete semantic correctness theorem for the terminating coefficient
projection: matching its finite polynomial signs gives an exact ordered table
of the whole input family, for arbitrary real specializations of the coefficient ring. -/
theorem projection_sign_table (qs : List R[X]) :
    ∀ (f g : R →+* ℝ),
      (∀ c ∈ projectionCoefficients qs, SameSign (f c) (g c)) →
      Nonempty (FamilyTable qs f g) := by
  classical
  apply projectionCoefficients_induction
    (fun qs cs => ∀ (f g : R →+* ℝ),
      (∀ c ∈ cs, SameSign (f c) (g c)) → Nonempty (FamilyTable qs f g))
  · intro rs hconst f g hcoef
    exact ⟨constant_family_table rs hconst f g hcoef⟩
  · intro rs hr ih f g hcoef
    let P := maxPolynomial rs hr
    let others := rs.erase P
    have hPspec := maxPolynomial_spec rs hr
    have hlow : ∀ c ∈ projectionCoefficients (lowerFamily P others), SameSign (f c) (g c) :=
      fun c hc => hcoef c (List.mem_cons_of_mem _ hc)
    obtain ⟨t⟩ := ih f g hlow
    change FamilyTable (lowerFamily P others) f g at t
    have hhead : SameSign (f P.leadingCoeff) (g P.leadingCoeff) := hcoef _ List.mem_cons_self
    have hwhole : ∀ c ∈ projectionCoefficients rs, SameSign (f c) (g c) := by
      rw [projectionCoefficients]
      simpa only [dif_pos hr] using hcoef
    have hzero := projected_zero_iff rs f g hwhole
    by_cases hf : f P.leadingCoeff = 0
    · have hg : g P.leadingCoeff = 0 := hhead.1.mp hf
      refine ⟨represented_table rs (lowerFamily P others) f g t ?_ hzero⟩
      intro S hS
      by_cases he : S = P
      · subst S
        exact ⟨P.eraseLead,eraseLead_mem_lowerFamily P others,
          (map_eraseLead_of_leading_zero P f hf).symm,
          (map_eraseLead_of_leading_zero P g hg).symm⟩
      · exact ⟨S,List.mem_append_left _ ((List.mem_erase_of_ne he).mpr hS),rfl,rfl⟩
    · have hg : g P.leadingCoeff ≠ 0 := by
        intro hg
        exact hf (hhead.1.mpr hg)
      let t' := nonzero_family_extension P others hPspec.2.1 f g hf hg t hlow hhead
      refine ⟨represented_table rs (P :: lowerFamily P others) f g t' ?_ hzero⟩
      intro S hS
      refine ⟨S,?_,rfl,rfl⟩
      by_cases he : S = P
      · exact List.mem_cons.mpr (Or.inl he)
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ ((List.mem_erase_of_ne he).mpr hS))

/-- In particular every realized sign vector transfers. This consequence is
used by existential elimination; its proof retains the stronger ordered invariant. -/
theorem projection_sign_witness (qs : List R[X]) (f g : R →+* ℝ)
    (hcoef : ∀ c ∈ projectionCoefficients qs, SameSign (f c) (g c)) (x : ℝ) :
    ∃ y, ∀ P ∈ qs, SameSign (P.eval₂ f x) (P.eval₂ g y) := by
  obtain ⟨t⟩ := projection_sign_table qs f g hcoef
  obtain ⟨y,hy⟩ := exists_position t.cuts x
  refine ⟨y,?_⟩
  simpa only [Polynomial.eval_map] using family_signs t x y hy

#print axioms projection_sign_table
#print axioms projection_sign_witness
#print axioms nonzero_family_extension
#print axioms represented_table
#print axioms constant_family_table
end LinearStochastic.RealQEProjectionCorrectness
