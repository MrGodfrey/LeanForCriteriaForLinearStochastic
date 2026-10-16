import Mathlib.Algebra.Polynomial.CancelLeads
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Denominator-free polynomial reduction for a real QE construction

This is a proved projection primitive, not a quantifier-elimination theorem.
The coefficient ring may itself be a multivariate polynomial ring. No division
by a parameter expression occurs in the construction. Even powers preserve
signs after every real specialization whose divisor leading coefficient is nonzero.
-/
noncomputable section
namespace LinearStochastic.RealQEPseudoDivision
open Polynomial
variable {R : Type*} [CommRing R]

/-- Repeated actual leading-term cancellation produces a polynomial identity and
a strictly smaller remainder, without dividing by the leading coefficient. -/
theorem exists_pseudodivision (P Q : R[X]) (hQ : Q ≠ 0) :
    ∃ (k : ℕ) (S T : R[X]),
      (C Q.leadingCoeff)^k * P = Q*S + T ∧ T.degree < Q.degree := by
  by_cases hqd : Q.natDegree = 0
  · have he : C Q.leadingCoeff = Q := by
      simpa only [leadingCoeff, hqd] using (eq_C_of_natDegree_eq_zero hqd).symm
    refine ⟨1,P,0,by simp [he],?_⟩
    simpa only [degree_zero, bot_lt_iff_ne_bot, ne_eq, degree_eq_bot] using hQ
  · induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
    | h n ih =>
      by_cases hsmall : P.degree < Q.degree
      · exact ⟨0,0,P,by simp,hsmall⟩
      · have hqp : Q.natDegree ≤ P.natDegree :=
          natDegree_le_natDegree (le_of_not_gt hsmall)
        have hpos : 0 < P.natDegree := lt_of_lt_of_le (Nat.pos_of_ne_zero hqd) hqp
        have hdrop : (Q.cancelLeads P).natDegree < n := by
          rw [← hn]
          exact natDegree_cancelLeads_lt_of_natDegree_le_natDegree hqp hpos
        obtain ⟨k,S,T,he,hT⟩ := ih _ hdrop (Q.cancelLeads P) rfl
        let L := C P.leadingCoeff * X^(P.natDegree-Q.natDegree)
        refine ⟨k+1,S+(C Q.leadingCoeff)^k*L,T,?_,hT⟩
        calc
          (C Q.leadingCoeff)^(k+1)*P =
              (C Q.leadingCoeff)^k*(Q.cancelLeads P) +
                Q*((C Q.leadingCoeff)^k*L) := by
            simp only [Polynomial.cancelLeads, Nat.sub_eq_zero_of_le hqp,
              pow_zero, mul_one, pow_succ, L]
            ring
          _ = Q*S + T + Q*((C Q.leadingCoeff)^k*L) := by rw [he]
          _ = Q*(S+(C Q.leadingCoeff)^k*L)+T := by ring

/-- An even scaling exponent makes every nondegenerate real specialization positive. -/
theorem exists_even_pseudodivision (P Q : R[X]) (hQ : Q ≠ 0) :
    ∃ (k : ℕ) (S T : R[X]),
      (C Q.leadingCoeff)^(2*k) * P = Q*S + T ∧ T.degree < Q.degree := by
  obtain ⟨k,S,T,he,hT⟩ := exists_pseudodivision P Q hQ
  refine ⟨k,(C Q.leadingCoeff)^k*S,(C Q.leadingCoeff)^k*T,?_,?_⟩
  · calc
      (C Q.leadingCoeff)^(2*k)*P = (C Q.leadingCoeff)^k*((C Q.leadingCoeff)^k*P) := by
        rw [two_mul, pow_add]
        ring
      _ = (C Q.leadingCoeff)^k*(Q*S+T) := by rw [he]
      _ = Q*((C Q.leadingCoeff)^k*S)+(C Q.leadingCoeff)^k*T := by ring
  · rw [← map_pow]
    rw [← smul_eq_C_mul]
    exact (degree_smul_le _ _).trans_lt hT

/-- Specializing a pseudo-division identity at a root of the divisor leaves the
scaled dividend equal to the lower-degree remainder. -/
theorem evaluate_even_remainder (P Q S T : R[X]) (k : ℕ)
    (hid : (C Q.leadingCoeff)^(2*k)*P = Q*S+T)
    (f : R →+* ℝ) (x : ℝ) (hroot : Q.eval₂ f x = 0) :
    (f Q.leadingCoeff)^(2*k)*P.eval₂ f x = T.eval₂ f x := by
  have h := congrArg (Polynomial.eval₂ f x) hid
  simpa [Polynomial.eval₂_mul, Polynomial.eval₂_pow, hroot] using h

/-- Zero and strict-positive signs of the dividend at divisor roots are recoverable
from the constructed lower-degree remainder, on the nonzero-leading-coefficient branch. -/
theorem signs_of_even_remainder (P Q S T : R[X]) (k : ℕ)
    (hid : (C Q.leadingCoeff)^(2*k)*P = Q*S+T)
    (f : R →+* ℝ) (x : ℝ) (hroot : Q.eval₂ f x = 0)
    (hlead : f Q.leadingCoeff ≠ 0) :
    (P.eval₂ f x = 0 ↔ T.eval₂ f x = 0) ∧
      (0 < P.eval₂ f x ↔ 0 < T.eval₂ f x) := by
  have he := evaluate_even_remainder P Q S T k hid f x hroot
  have hp : 0 < (f Q.leadingCoeff)^(2*k) := by
    rw [pow_mul]
    exact pow_pos (sq_pos_of_ne_zero hlead) _
  rw [← he]
  exact ⟨(mul_eq_zero_iff_left hp.ne').symm, (mul_pos_iff_of_pos_left hp).symm⟩

/-- The lower-degree sign test is produced from the input polynomials; it is not
provided as an assumed oracle. Its identities hold simultaneously for every real
specialization of every parameter coefficient. -/
theorem exists_sign_preserving_remainder (P Q : R[X]) (hQ : Q ≠ 0) :
    ∃ T : R[X], T.degree < Q.degree ∧
      ∀ (f : R →+* ℝ) (x : ℝ), Q.eval₂ f x = 0 → f Q.leadingCoeff ≠ 0 →
        (P.eval₂ f x = 0 ↔ T.eval₂ f x = 0) ∧
          (0 < P.eval₂ f x ↔ 0 < T.eval₂ f x) := by
  obtain ⟨k,S,T,hid,hT⟩ := exists_even_pseudodivision P Q hQ
  exact ⟨T,hT,fun f x hroot hlead => signs_of_even_remainder P Q S T k hid f x hroot hlead⟩

/-- The degenerate leading-coefficient branch is handled by actual erasure, not by
inverting a coefficient that can specialize to zero. -/
theorem evaluate_eraseLead_of_leading_zero (P : R[X]) (f : R →+* ℝ) (x : ℝ)
    (hlead : f P.leadingCoeff = 0) : P.eraseLead.eval₂ f x = P.eval₂ f x := by
  have h := congrArg (Polynomial.eval₂ f x) P.eraseLead_add_C_mul_X_pow
  simpa only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, hlead, zero_mul, add_zero] using h

#print axioms exists_sign_preserving_remainder
#print axioms exists_even_pseudodivision
#print axioms signs_of_even_remainder
#print axioms evaluate_eraseLead_of_leading_zero
end LinearStochastic.RealQEPseudoDivision
