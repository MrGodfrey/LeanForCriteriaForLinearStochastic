module

public import LinearStochastic.RealQEPseudoDivision
public import Mathlib.Algebra.Polynomial.Derivative

@[expose] public section

/-!
# Finite remainder closure for symbolic real projection

For a fixed higher-degree polynomial P, this constructs a finite family closed
under sign-preserving remainders of P. Such a closure is needed because newly
introduced remainder roots themselves become sign-cell boundaries. All members
are actual polynomials in the coefficient ring, not specialization-dependent values.
The full parameter sign-table induction is still separate.
-/
noncomputable section
namespace LinearStochastic.RealQEProjection
open Polynomial RealQEPseudoDivision
variable {R : Type*} [CommRing R]

/-- A real-sign-preserving remainder selected from the proved pseudo-division construction. -/
def remainder (P Q : R[X]) : R[X] := by
  classical
  exact if hQ : Q = 0 then 0 else Classical.choose (exists_sign_preserving_remainder P Q hQ)

theorem remainder_degree_lt (P Q : R[X]) (hQ : Q ≠ 0) :
    (remainder P Q).degree < Q.degree := by
  simpa only [remainder, dif_neg hQ] using
    (Classical.choose_spec (exists_sign_preserving_remainder P Q hQ)).1

theorem remainder_signs (P Q : R[X]) (hQ : Q ≠ 0) (f : R →+* ℝ) (x : ℝ)
    (hroot : Q.eval₂ f x = 0) (hlead : f Q.leadingCoeff ≠ 0) :
    (P.eval₂ f x = 0 ↔ (remainder P Q).eval₂ f x = 0) ∧
      (0 < P.eval₂ f x ↔ 0 < (remainder P Q).eval₂ f x) := by
  simpa only [remainder, dif_neg hQ] using
    (Classical.choose_spec (exists_sign_preserving_remainder P Q hQ)).2 f x hroot hlead

theorem remainder_natDegree_lt (P Q : R[X]) (hq : Q.natDegree ≠ 0) :
    (remainder P Q).natDegree < Q.natDegree := by
  have hQ : Q ≠ 0 := by intro h; simp [h] at hq
  by_cases hR : remainder P Q = 0
  · simpa [hR] using Nat.pos_of_ne_zero hq
  · exact natDegree_lt_natDegree hR (remainder_degree_lt P Q hQ)

/-- Descend in the divisor's actual degree until a constant is reached. -/
def remainderChain (P Q : R[X]) : List R[X] :=
  if _hq : Q.natDegree = 0 then [Q]
  else Q :: remainderChain P (remainder P Q)
termination_by Q.natDegree
decreasing_by exact remainder_natDegree_lt P Q _hq

theorem mem_remainderChain_self (P Q : R[X]) : Q ∈ remainderChain P Q := by
  rw [remainderChain]
  split <;> simp

/-- The symbolic closure is finite with an explicit degree bound on its length. -/
theorem remainderChain_length_le (P Q : R[X]) :
    (remainderChain P Q).length ≤ Q.natDegree+1 := by
  fun_induction remainderChain P Q with
  | case1 Q hq => simp [hq]
  | case2 Q hq ih =>
    simp only [List.length_cons]
    have hd := remainder_natDegree_lt P Q hq
    omega

/-- Every member of positive degree has its required remainder in the same finite chain. -/
theorem remainderChain_closed (P Q S : R[X]) (hS : S ∈ remainderChain P Q)
    (hs : S.natDegree ≠ 0) : remainder P S ∈ remainderChain P Q := by
  fun_induction remainderChain P Q with
  | case1 Q hq =>
    simp only [List.mem_singleton] at hS
    subst S
    exact False.elim (hs hq)
  | case2 Q hq ih =>
    rcases List.mem_cons.mp hS with h | h
    · subst S
      exact List.mem_cons_of_mem _ (mem_remainderChain_self P (remainder P Q))
    · exact List.mem_cons_of_mem _ (ih h)

/-- Reconstructed boundary signs are available from members of the actual finite closure. -/
theorem remainderChain_boundary_signs (P Q S : R[X]) (hS : S ∈ remainderChain P Q)
    (hs : S.natDegree ≠ 0) :
    ∃ T ∈ remainderChain P Q, T.degree < S.degree ∧
      ∀ (f : R →+* ℝ) (x : ℝ), S.eval₂ f x = 0 → f S.leadingCoeff ≠ 0 →
        (P.eval₂ f x = 0 ↔ T.eval₂ f x = 0) ∧
          (0 < P.eval₂ f x ↔ 0 < T.eval₂ f x) := by
  have hSn : S ≠ 0 := by intro h; simp [h] at hs
  exact ⟨remainder P S,remainderChain_closed P Q S hS hs,remainder_degree_lt P S hSn,
    fun f x hr hl => remainder_signs P S hSn f x hr hl⟩

/-- Include the derivative and every original boundary polynomial, then close each
under the fixed dividend's sign-preserving remainders. -/
def projectionClosure (P : R[X]) (qs : List R[X]) : List R[X] :=
  (P.derivative :: qs).flatMap (remainderChain P)

theorem derivative_mem_projectionClosure (P : R[X]) (qs : List R[X]) :
    P.derivative ∈ projectionClosure P qs := by
  apply List.mem_flatMap.mpr
  exact ⟨P.derivative,by simp,mem_remainderChain_self P P.derivative⟩

theorem mem_projectionClosure (P Q : R[X]) (qs : List R[X]) (hQ : Q ∈ qs) :
    Q ∈ projectionClosure P qs := by
  apply List.mem_flatMap.mpr
  exact ⟨Q,List.mem_cons_of_mem _ hQ,mem_remainderChain_self P Q⟩

theorem projectionClosure_closed (P S : R[X]) (qs : List R[X])
    (hS : S ∈ projectionClosure P qs) (hs : S.natDegree ≠ 0) :
    remainder P S ∈ projectionClosure P qs := by
  obtain ⟨Q,hQ,hSQ⟩ := List.mem_flatMap.mp hS
  exact List.mem_flatMap.mpr ⟨Q,hQ,remainderChain_closed P Q S hSQ hs⟩

theorem eraseLead_natDegree_lt (Q : R[X]) (hq : Q.natDegree ≠ 0) :
    Q.eraseLead.natDegree < Q.natDegree := by
  have hQ : Q ≠ 0 := by intro h; simp [h] at hq
  by_cases hR : Q.eraseLead = 0
  · simpa [hR] using Nat.pos_of_ne_zero hq
  · exact natDegree_lt_natDegree hR (degree_eraseLead_lt hQ)

/-- A finite closure containing both nonzero-leading-coefficient remainder branches
and zero-leading-coefficient erasure branches. Both recursive edges lower actual degree. -/
def branchClosure (P Q : R[X]) : List R[X] :=
  if _hq : Q.natDegree = 0 then [Q]
  else Q :: (branchClosure P (remainder P Q) ++ branchClosure P Q.eraseLead)
termination_by Q.natDegree
decreasing_by
  · exact remainder_natDegree_lt P Q _hq
  · exact eraseLead_natDegree_lt Q _hq

theorem mem_branchClosure_self (P Q : R[X]) : Q ∈ branchClosure P Q := by
  rw [branchClosure]
  split <;> simp

/-- Every branch stays below the initial divisor degree. -/
theorem branchClosure_degree_le (P Q S : R[X]) (hS : S ∈ branchClosure P Q) :
    S.degree ≤ Q.degree := by
  fun_induction branchClosure P Q with
  | case1 Q hq =>
    simp only [List.mem_singleton] at hS
    exact le_of_eq (congrArg Polynomial.degree hS)
  | case2 Q hq ihr ihe =>
    have hQ : Q ≠ 0 := by intro h; simp [h] at hq
    rcases List.mem_cons.mp hS with h | h
    · exact le_of_eq (congrArg Polynomial.degree h)
    · rcases List.mem_append.mp h with h | h
      · exact (ihr h).trans (remainder_degree_lt P Q hQ).le
      · exact (ihe h).trans (degree_eraseLead_lt hQ).le

/-- Every newly introduced member is strictly lower degree. This is the degree
invariant needed by a later maximum-degree sign-table recursion. -/
theorem branchClosure_tail_degree_lt (P Q S : R[X])
    (hS : S ∈ (branchClosure P Q).tail) : S.degree < Q.degree := by
  rw [branchClosure] at hS
  split at hS
  · simp at hS
  · rename_i hq
    have hQ : Q ≠ 0 := by intro h; simp [h] at hq
    simp only [List.tail_cons, List.mem_append] at hS
    rcases hS with h | h
    · exact (branchClosure_degree_le P (remainder P Q) S h).trans_lt (remainder_degree_lt P Q hQ)
    · exact (branchClosure_degree_le P Q.eraseLead S h).trans_lt (degree_eraseLead_lt hQ)

/-- The closure includes the true polynomial required in either leading-coefficient branch. -/
theorem branchClosure_closed (P Q S : R[X]) (hS : S ∈ branchClosure P Q)
    (hs : S.natDegree ≠ 0) :
    remainder P S ∈ branchClosure P Q ∧ S.eraseLead ∈ branchClosure P Q := by
  fun_induction branchClosure P Q with
  | case1 Q hq =>
    simp only [List.mem_singleton] at hS
    subst S
    exact False.elim (hs hq)
  | case2 Q hq ihr ihe =>
    rcases List.mem_cons.mp hS with h | h
    · subst S
      exact ⟨List.mem_cons_of_mem _ (List.mem_append_left _ (mem_branchClosure_self P (remainder P Q))),
        List.mem_cons_of_mem _ (List.mem_append_right _ (mem_branchClosure_self P Q.eraseLead))⟩
    · rcases List.mem_append.mp h with h | h
      · obtain ⟨hr,he⟩ := ihr h
        exact ⟨List.mem_cons_of_mem _ (List.mem_append_left _ hr),
          List.mem_cons_of_mem _ (List.mem_append_left _ he)⟩
      · obtain ⟨hr,he⟩ := ihe h
        exact ⟨List.mem_cons_of_mem _ (List.mem_append_right _ hr),
          List.mem_cons_of_mem _ (List.mem_append_right _ he)⟩

/-- The zero-leading branch preserves the complete specialized polynomial, not only
its value at a particular proposed root. -/
theorem map_eraseLead_of_leading_zero (Q : R[X]) (f : R →+* ℝ)
    (hl : f Q.leadingCoeff = 0) : Q.eraseLead.map f = Q.map f := by
  have h := congrArg (Polynomial.map f) Q.eraseLead_add_C_mul_X_pow
  simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, hl, Polynomial.C_0, zero_mul, add_zero] using h

/-- Every nonzero real specialization has a member of the finite symbolic closure
with exactly the same specialized polynomial and a nonvanishing symbolic leading coefficient. -/
theorem branchClosure_specialization (P Q : R[X]) (f : R →+* ℝ) (hQ : Q.map f ≠ 0) :
    ∃ S ∈ branchClosure P Q, S.map f = Q.map f ∧ f S.leadingCoeff ≠ 0 := by
  fun_induction branchClosure P Q with
  | case1 Q hq =>
    refine ⟨Q,by simp,rfl,?_⟩
    intro hl
    have he : Q = C Q.leadingCoeff := by
      simpa only [leadingCoeff,hq] using eq_C_of_natDegree_eq_zero hq
    apply hQ
    rw [he]
    simp only [Polynomial.map_C,hl,Polynomial.C_0]
  | case2 Q hq ihr ihe =>
    by_cases hl : f Q.leadingCoeff = 0
    · have he := map_eraseLead_of_leading_zero Q f hl
      obtain ⟨S,hS,hmap,hlS⟩ := ihe (he ▸ hQ)
      exact ⟨S,List.mem_cons_of_mem _ (List.mem_append_right _ hS),hmap.trans he,hlS⟩
    · exact ⟨Q,by simp,rfl,hl⟩

#print axioms branchClosure_tail_degree_lt
#print axioms branchClosure_closed
#print axioms branchClosure_specialization
#print axioms remainderChain_length_le
#print axioms remainderChain_boundary_signs
#print axioms projectionClosure_closed
end LinearStochastic.RealQEProjection
