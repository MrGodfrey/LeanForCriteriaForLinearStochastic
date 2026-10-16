import LinearStochastic.RealQEProjection
import Mathlib.Data.Multiset.DershowitzManna
import Mathlib.Data.Finset.Max

/-!
# Terminating symbolic projection recursion

This constructs the finite coefficient family for a Cohen–Hörmander style
projection recursion. It proves the multiset degree descent and preserves every
remainder/degree-drop branch needed by a later sign-table correctness proof.
The correctness of the final projected sign table is not asserted here.
-/
noncomputable section
namespace LinearStochastic.RealQERecursiveProjection
open Polynomial RealQEProjection
variable {R : Type*} [CommRing R]

/-- Additional polynomials after removing the chosen maximal-degree dividend.
The other original polynomials are retained separately, without duplication. -/
def additions (P : R[X]) (qs : List R[X]) : List R[X] :=
  branchClosure P P.derivative ++ branchClosure P P.eraseLead ++
    qs.flatMap (fun Q => (branchClosure P Q).tail)

def lowerFamily (P : R[X]) (qs : List R[X]) : List R[X] := qs ++ additions P qs

theorem additions_natDegree_lt (P : R[X]) (qs : List R[X])
    (hp : P.natDegree ≠ 0) (hmax : ∀ Q ∈ qs, Q.natDegree ≤ P.natDegree)
    (S : R[X]) (hs : S ∈ additions P qs) : S.natDegree < P.natDegree := by
  have hP : P ≠ 0 := by intro h; simp [h] at hp
  have degree_to_nat {U V : R[X]} (hd : U.degree ≤ V.degree) : U.natDegree ≤ V.natDegree :=
    Polynomial.natDegree_le_natDegree hd
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_append.mp hs with hs | hs
    · exact (degree_to_nat (branchClosure_degree_le P P.derivative S hs)).trans_lt
        (Polynomial.natDegree_derivative_lt hp)
    · exact (degree_to_nat (branchClosure_degree_le P P.eraseLead S hs)).trans_lt
        (eraseLead_natDegree_lt P hp)
  · obtain ⟨Q,hQ,hs⟩ := List.mem_flatMap.mp hs
    have hd := branchClosure_tail_degree_lt P Q S hs
    by_cases hS : S = 0
    · simpa [hS] using Nat.pos_of_ne_zero hp
    · exact (Polynomial.natDegree_lt_natDegree hS hd).trans_le (hmax Q hQ)

/-- The actual multiset measure, counting repeated polynomial occurrences. -/
def degreeMeasure (qs : List R[X]) : Multiset ℕ := (qs.map Polynomial.natDegree : List ℕ)

/-- Removing one maximal polynomial and introducing arbitrarily many strictly
lower-degree polynomials is a genuine well-founded multiset descent. -/
theorem lowerFamily_degree_descent (P : R[X]) (qs : List R[X])
    (hp : P.natDegree ≠ 0) (hmax : ∀ Q ∈ qs, Q.natDegree ≤ P.natDegree) :
    Multiset.IsDershowitzMannaLT (degreeMeasure (lowerFamily P qs))
      (degreeMeasure (P :: qs)) := by
  refine ⟨degreeMeasure qs, degreeMeasure (additions P qs), {P.natDegree}, ?_, ?_, ?_, ?_⟩
  · simp
  · simp [degreeMeasure, lowerFamily]
  · change P.natDegree ::ₘ degreeMeasure qs = degreeMeasure qs + {P.natDegree}
    simp [Multiset.add_comm]
  · intro d hd
    obtain ⟨S,hS,rfl⟩ := List.mem_map.mp (show d ∈ (additions P qs).map Polynomial.natDegree from hd)
    exact ⟨P.natDegree,by simp,additions_natDegree_lt P qs hp hmax S hS⟩

/-- Every removed polynomial has its original derivative in the recursive input. -/
theorem derivative_mem_lowerFamily (P : R[X]) (qs : List R[X]) :
    P.derivative ∈ lowerFamily P qs := by
  exact List.mem_append_right _ (List.mem_append_left _
    (List.mem_append_left _ (mem_branchClosure_self P P.derivative)))

theorem eraseLead_mem_lowerFamily (P : R[X]) (qs : List R[X]) :
    P.eraseLead ∈ lowerFamily P qs := by
  exact List.mem_append_right _ (List.mem_append_left _
    (List.mem_append_right _ (mem_branchClosure_self P P.eraseLead)))

theorem branchClosure_mem_lowerFamily (P : R[X]) (qs : List R[X])
    (Q : R[X]) (hQ : Q ∈ qs) (S : R[X]) (hS : S ∈ branchClosure P Q) :
    S ∈ lowerFamily P qs := by
  by_cases hSQ : S = Q
  · subst S
    exact List.mem_append_left _ hQ
  · have ht : S ∈ (branchClosure P Q).tail := by
      rw [branchClosure] at hS ⊢
      by_cases hq : Q.natDegree = 0
      · simp [hq] at hS
        exact False.elim (hSQ hS)
      · simpa [hq, hSQ] using hS
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨Q,hQ,ht⟩))

/-- The recursive input is closed under the two operations needed at every
nonconstant boundary polynomial, including boundaries added by the recursion. -/
theorem lowerFamily_closed (P : R[X]) (qs : List R[X]) (S : R[X])
    (hs : S ∈ lowerFamily P qs) (hd : S.natDegree ≠ 0) :
    remainder P S ∈ lowerFamily P qs ∧ S.eraseLead ∈ lowerFamily P qs := by
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨hr,he⟩ := branchClosure_closed P S S (mem_branchClosure_self P S) hd
    exact ⟨branchClosure_mem_lowerFamily P qs S hs _ hr,
      branchClosure_mem_lowerFamily P qs S hs _ he⟩
  · rcases List.mem_append.mp hs with hs | hs
    · rcases List.mem_append.mp hs with hs | hs
      · obtain ⟨hr,he⟩ := branchClosure_closed P P.derivative S hs hd
        exact ⟨List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hr)),
          List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ he))⟩
      · obtain ⟨hr,he⟩ := branchClosure_closed P P.eraseLead S hs hd
        exact ⟨List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hr)),
          List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ he))⟩
    · obtain ⟨Q,hQ,hs⟩ := List.mem_flatMap.mp hs
      obtain ⟨hr,he⟩ := branchClosure_closed P Q S (List.mem_of_mem_tail hs) hd
      exact ⟨branchClosure_mem_lowerFamily P qs Q hQ _ hr,
        branchClosure_mem_lowerFamily P qs Q hQ _ he⟩

/-- Closure is transitive: all descendants of an already retained boundary
remain in the same recursive family. -/
theorem branchClosure_contained (P Q : R[X]) (T : R[X] → Prop)
    (hclosed : ∀ S, T S → S.natDegree ≠ 0 → T (remainder P S) ∧ T S.eraseLead) :
    T Q → ∀ S ∈ branchClosure P Q, T S := by
  fun_induction branchClosure P Q with
  | case1 Q hq =>
    intro hQ S hS
    have he : S = Q := List.mem_singleton.mp hS
    exact he ▸ hQ
  | case2 Q hq ihr ihe =>
    intro hQ S hS
    rcases List.mem_cons.mp hS with h | h
    · exact h ▸ hQ
    · obtain ⟨hr,he⟩ := hclosed Q hQ hq
      rcases List.mem_append.mp h with h | h
      · exact ihr hr S h
      · exact ihe he S h

theorem lowerFamily_branchClosure (P Q : R[X]) (qs : List R[X])
    (hQ : Q ∈ lowerFamily P qs) :
    ∀ S ∈ branchClosure P Q, S ∈ lowerFamily P qs :=
  branchClosure_contained P Q (fun S => S ∈ lowerFamily P qs)
    (fun S hs hd => lowerFamily_closed P qs S hs hd) hQ

/-- Select a maximal-degree polynomial only when a positive-degree one exists. -/
def HasPositiveDegree (qs : List R[X]) : Prop := ∃ P ∈ qs, P.natDegree ≠ 0

theorem exists_max_polynomial (qs : List R[X]) (hq : HasPositiveDegree qs) :
    ∃ P ∈ qs, P.natDegree ≠ 0 ∧ ∀ Q ∈ qs, Q.natDegree ≤ P.natDegree := by
  classical
  obtain ⟨Q,hQ,hd⟩ := hq
  obtain ⟨P,hP,hmax⟩ := Finset.exists_max_image qs.toFinset Polynomial.natDegree
    ⟨Q,List.mem_toFinset.mpr hQ⟩
  refine ⟨P,List.mem_toFinset.mp hP,?_,fun S hS => hmax S (List.mem_toFinset.mpr hS)⟩
  have hm := hmax Q (List.mem_toFinset.mpr hQ)
  omega

def maxPolynomial (qs : List R[X]) (hq : HasPositiveDegree qs) : R[X] :=
  Classical.choose (exists_max_polynomial qs hq)

theorem maxPolynomial_spec (qs : List R[X]) (hq : HasPositiveDegree qs) :
    maxPolynomial qs hq ∈ qs ∧ (maxPolynomial qs hq).natDegree ≠ 0 ∧
      ∀ Q ∈ qs, Q.natDegree ≤ (maxPolynomial qs hq).natDegree :=
  Classical.choose_spec (exists_max_polynomial qs hq)

def reducedFamily (qs : List R[X]) (hq : HasPositiveDegree qs) : List R[X] := by
  classical
  exact lowerFamily (maxPolynomial qs hq) (qs.erase (maxPolynomial qs hq))

theorem degreeMeasure_perm {qs rs : List R[X]} (h : qs.Perm rs) :
    degreeMeasure qs = degreeMeasure rs :=
  Multiset.coe_eq_coe.mpr (h.map Polynomial.natDegree)

theorem reducedFamily_descent (qs : List R[X]) (hq : HasPositiveDegree qs) :
    Multiset.IsDershowitzMannaLT (degreeMeasure (reducedFamily qs hq)) (degreeMeasure qs) := by
  classical
  obtain ⟨hm,hp,hmax⟩ := maxPolynomial_spec qs hq
  have he := degreeMeasure_perm (List.perm_cons_erase hm)
  rw [he]
  exact lowerFamily_degree_descent _ _ hp (fun Q hQ => hmax Q (List.mem_of_mem_erase hQ))

/-- A concrete finite coefficient family. Termination uses the well-founded
multiset order; one removed degree may be replaced by any finite number of smaller ones. -/
def projectionCoefficients (qs : List R[X]) : List R := by
  classical
  exact if hq : HasPositiveDegree qs then
    (maxPolynomial qs hq).leadingCoeff :: projectionCoefficients (reducedFamily qs hq)
  else qs.map (fun P => P.coeff 0)
termination_by degreeMeasure qs
decreasing_by exact reducedFamily_descent qs hq

/-- Exact induction rule for proving a semantic invariant of the concrete
coefficient recursion. The high-degree semantic step must still be proved by its caller. -/
theorem projectionCoefficients_induction
    (T : List R[X] → List R → Prop)
    (hconstant : ∀ qs, (∀ P ∈ qs, P.natDegree = 0) → T qs (qs.map (fun P => P.coeff 0)))
    (hstep : ∀ qs (hq : HasPositiveDegree qs),
      T (reducedFamily qs hq) (projectionCoefficients (reducedFamily qs hq)) →
      T qs ((maxPolynomial qs hq).leadingCoeff :: projectionCoefficients (reducedFamily qs hq))) :
    ∀ qs, T qs (projectionCoefficients qs) := by
  intro qs
  fun_induction projectionCoefficients qs with
  | case1 qs hq ih => exact hstep qs hq ih
  | case2 qs hq =>
    apply hconstant qs
    intro P hP
    by_contra hp
    exact hq ⟨P,hP,hp⟩

/-- Every input leading coefficient is explicitly tested by the finite recursion. -/
theorem leadingCoeff_mem_projectionCoefficients (qs : List R[X]) :
    ∀ P ∈ qs, P.leadingCoeff ∈ projectionCoefficients qs := by
  classical
  apply projectionCoefficients_induction (fun qs cs => ∀ P ∈ qs, P.leadingCoeff ∈ cs)
  · intro rs hrs P hP
    apply List.mem_map.mpr
    exact ⟨P,hP,by simp only [Polynomial.leadingCoeff,hrs P hP]⟩
  · intro rs hr ih P hP
    by_cases he : P = maxPolynomial rs hr
    · subst P
      exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      apply ih P
      exact List.mem_append_left _ ((List.mem_erase_of_ne he).mpr hP)

/-- In fact every nonzero symbolic coefficient is tested: erasing a vanished
leading term cannot lose any later degree or sign branch. -/
theorem coeff_mem_projectionCoefficients (qs : List R[X]) :
    ∀ P ∈ qs, ∀ k, P.coeff k ≠ 0 → P.coeff k ∈ projectionCoefficients qs := by
  classical
  apply projectionCoefficients_induction
    (fun qs cs => ∀ P ∈ qs, ∀ k, P.coeff k ≠ 0 → P.coeff k ∈ cs)
  · intro rs hrs P hP k hk
    have hkzero : k = 0 := by
      have hle := Polynomial.le_natDegree_of_ne_zero hk
      have hd := hrs P hP
      omega
    subst k
    exact List.mem_map.mpr ⟨P,hP,rfl⟩
  · intro rs hr ih P hP k hk
    by_cases he : P = maxPolynomial rs hr
    · subst P
      by_cases hd : k = (maxPolynomial rs hr).natDegree
      · subst k
        exact List.mem_cons_self
      · have hc := Polynomial.eraseLead_coeff_of_ne (f := maxPolynomial rs hr) k hd
        apply List.mem_cons_of_mem
        rw [← hc]
        exact ih _ (eraseLead_mem_lowerFamily _ _) k (hc ▸ hk)
    · apply List.mem_cons_of_mem
      exact ih P (List.mem_append_left _ ((List.mem_erase_of_ne he).mpr hP)) k hk

#print axioms coeff_mem_projectionCoefficients
#print axioms projectionCoefficients
#print axioms projectionCoefficients_induction

#print axioms lowerFamily_degree_descent
#print axioms lowerFamily_closed
end LinearStochastic.RealQERecursiveProjection
