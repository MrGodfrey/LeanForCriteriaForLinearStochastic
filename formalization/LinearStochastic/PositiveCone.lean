module

public import Mathlib
public import LinearStochastic.OpenConeAlternative

@[expose] public section

/-!
# The open cone of uniformly positive symmetric operators

The positivity margin is an explicit quadratic-form bound. It implies the
strict positive definiteness required by the LMI. This cone is open and convex
and contains the identity, so it can be used in the proved separation theorem.
-/
noncomputable section
namespace LinearStochastic.PositiveCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Positive definiteness with a uniform quadratic-form margin. -/
def UniformPositive (T : E →L[ℝ] E) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ x, ε * ‖x‖ ^ 2 ≤ inner ℝ (T x) x

theorem uniformPositive_strict (T : E →L[ℝ] E) (h : UniformPositive T)
    (x : E) (hx : x ≠ 0) : 0 < inner ℝ (T x) x := by
  obtain ⟨ε, hε, hbound⟩ := h
  exact lt_of_lt_of_le (mul_pos hε (sq_pos_of_pos (norm_pos_iff.mpr hx))) (hbound x)

theorem uniformPositive_id : UniformPositive (ContinuousLinearMap.id ℝ E) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro x
  simp [real_inner_self_eq_norm_sq]

/-- Positivity persists inside a norm ball of radius equal to its margin. -/
theorem uniformPositive_of_norm_sub_lt (T S : E →L[ℝ] E) (ε : ℝ)
    (hε : 0 < ε) (hT : ∀ x, ε * ‖x‖ ^ 2 ≤ inner ℝ (T x) x)
    (hclose : ‖S - T‖ < ε) : UniformPositive S := by
  refine ⟨ε - ‖S - T‖, sub_pos.mpr hclose, ?_⟩
  intro x
  have hinner := neg_le_of_abs_le (abs_real_inner_le_norm ((S - T) x) x)
  have hop := mul_le_mul_of_nonneg_right ((S - T).le_opNorm x) (norm_nonneg x)
  simp only [ContinuousLinearMap.sub_apply, inner_sub_left] at hinner hop
  nlinarith [hT x]

/-- The actual cone lives in the real vector space of symmetric operators. -/
def cone : Set (selfAdjoint (E →L[ℝ] E)) := {T | UniformPositive T.val}

theorem cone_nonempty : (cone (E := E)).Nonempty :=
  ⟨⟨ContinuousLinearMap.id ℝ E, by
      change IsSelfAdjoint (1 : E →L[ℝ] E)
      exact IsSelfAdjoint.one (E →L[ℝ] E)⟩, uniformPositive_id⟩

theorem cone_isOpen : IsOpen (cone (E := E)) := by
  rw [Metric.isOpen_iff]
  intro T hT
  obtain ⟨ε, hε, hbound⟩ := hT
  refine ⟨ε, hε, ?_⟩
  intro S hS
  apply uniformPositive_of_norm_sub_lt T.val S.val ε hε hbound
  simpa [Metric.mem_ball, dist_eq_norm] using hS

theorem cone_convex : Convex ℝ (cone (E := E)) := by
  intro T hT S hS a b ha hb hab
  obtain ⟨ε, hε, hT⟩ := hT
  obtain ⟨δ, hδ, hS⟩ := hS
  have hpos : 0 < a * ε + b * δ := by
    by_cases ha0 : a = 0
    · subst a
      simp only [zero_add] at hab
      simp [hab, hδ]
    · have hprod := mul_pos (lt_of_le_of_ne ha (Ne.symm ha0)) hε
      have hprod' := mul_nonneg hb hδ.le
      linarith
  refine ⟨a * ε + b * δ, hpos, ?_⟩
  intro x
  change (a * ε + b * δ) * ‖x‖ ^ 2 ≤ inner ℝ ((a • T.val + b • S.val) x) x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_left, real_inner_smul_left]
  have ht := mul_le_mul_of_nonneg_left (hT x) ha
  have hs := mul_le_mul_of_nonneg_left (hS x) hb
  nlinarith

/-- Applying separation to this concrete positivity cone requires no
unproved semidefinite duality or closed-image assumption. -/
theorem strict_positive_or_certificate (L : Submodule ℝ (selfAdjoint (E →L[ℝ] E))) :
    (∃ T, T ∈ L ∧ UniformPositive T.val) ∨
    (∃ f : selfAdjoint (E →L[ℝ] E) →L[ℝ] ℝ,
      f ≠ 0 ∧ (∀ T ∈ L, f T = 0) ∧ ∀ T, UniformPositive T.val → 0 < f T) := by
  exact OpenConeAlternative.strict_feasibility_or_certificate
    (E := selfAdjoint (E →L[ℝ] E)) L (cone (E := E))
    (cone_convex (E := E)) (cone_isOpen (E := E)) (cone_nonempty (E := E))

end LinearStochastic.PositiveCone
