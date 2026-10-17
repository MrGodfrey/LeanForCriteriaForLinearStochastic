module

public import LinearStochastic.PositiveCone
public import LinearStochastic.ConeCertificate

@[expose] public section
noncomputable section
namespace LinearStochastic.PositiveDual
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def tracePair : (E →ₗ[ℝ] E) →ₗ[ℝ] Module.Dual ℝ (E →ₗ[ℝ] E) where
  toFun Q :=
    { toFun := fun T => LinearMap.trace ℝ E (Q.comp T)
      map_add' := by intros; simp [LinearMap.comp_add]
      map_smul' := by intros; simp [LinearMap.comp_smul] }
  map_add' := by intros; ext; simp [LinearMap.add_comp]
  map_smul' := by intros; ext; simp [LinearMap.smul_comp]

theorem tracePair_rankOne (Q : E →ₗ[ℝ] E) (x y : E) :
    tracePair Q (rankOne ℝ x y).toLinearMap = inner ℝ y (Q x) := by
  change LinearMap.trace ℝ E (Q.comp ((innerₛₗ ℝ y).smulRight x)) = _
  have h : Q.comp ((innerₛₗ ℝ y).smulRight x) = (innerₛₗ ℝ y).smulRight (Q x) := by
    ext z
    simp
  rw [h, LinearMap.trace_smulRight]
  rfl

theorem tracePair_injective : Function.Injective (tracePair (E := E)) := by
  intro Q R h
  ext x
  apply ext_inner_left ℝ
  intro y
  have hh := LinearMap.congr_fun h (rankOne ℝ x y).toLinearMap
  simpa only [tracePair_rankOne] using hh

theorem trace_representation (f : Module.Dual ℝ (E →ₗ[ℝ] E)) :
    ∃ Q : E →ₗ[ℝ] E, ∀ T, f T = LinearMap.trace ℝ E (Q.comp T) := by
  have hs : Function.Surjective (tracePair (E := E)) := by
    apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp tracePair_injective
    simp [Module.finrank_linearMap]
  obtain ⟨Q, hQ⟩ := hs f
  exact ⟨Q, fun T => (LinearMap.congr_fun hQ T).symm⟩

end LinearStochastic.PositiveDual

namespace LinearStochastic.PositiveDual
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def symmetricExtension (f : selfAdjoint (E →L[ℝ] E) →L[ℝ] ℝ) :
    Module.Dual ℝ (E →ₗ[ℝ] E) :=
  f.toLinearMap.comp ((selfAdjointPart ℝ).comp
    (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] E) ≃ₗ[ℝ] E →L[ℝ] E).toLinearMap)

theorem symmetricExtension_adjoint (f : selfAdjoint (E →L[ℝ] E) →L[ℝ] ℝ)
    (T : E →ₗ[ℝ] E) : symmetricExtension f T.adjoint = symmetricExtension f T := by
  change f (selfAdjointPart ℝ T.adjoint.toContinuousLinearMap) =
    f (selfAdjointPart ℝ T.toContinuousLinearMap)
  congr 1
  apply Subtype.ext
  simp [selfAdjointPart_apply_coe, LinearMap.adjoint_toContinuousLinearMap,
    ContinuousLinearMap.star_eq_adjoint, add_comm]

theorem symmetricExtension_selfAdjoint (f : selfAdjoint (E →L[ℝ] E) →L[ℝ] ℝ)
    (T : selfAdjoint (E →L[ℝ] E)) : symmetricExtension f T.val.toLinearMap = f T := by
  change f (selfAdjointPart ℝ T.val) = f T
  rw [T.property.selfAdjointPart_apply ℝ]

theorem symmetric_trace_representation (f : selfAdjoint (E →L[ℝ] E) →L[ℝ] ℝ) :
    ∃ Q : E →ₗ[ℝ] E, Q.IsSymmetric ∧
      ∀ T : selfAdjoint (E →L[ℝ] E), f T = LinearMap.trace ℝ E (Q.comp T.val.toLinearMap) := by
  obtain ⟨Q, hQ⟩ := trace_representation (symmetricExtension f)
  have hr (x y : E) : symmetricExtension f (rankOne ℝ x y).toLinearMap = inner ℝ y (Q x) := by
    rw [hQ]
    exact tracePair_rankOne Q x y
  have hsym : Q.IsSymmetric := by
    intro x y
    have h := symmetricExtension_adjoint f (rankOne ℝ x y).toLinearMap
    rw [ContinuousLinearMap.adjoint_toLinearMap, adjoint_rankOne, hr, hr] at h
    rw [real_inner_comm]
    exact h.symm
  refine ⟨Q, hsym, ?_⟩
  intro T
  rw [← symmetricExtension_selfAdjoint f T]
  exact hQ T.val.toLinearMap
end LinearStochastic.PositiveDual

namespace LinearStochastic.PositiveDual
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def rankOneSelf (v : E) : selfAdjoint (E →L[ℝ] E) :=
  ⟨rankOne ℝ v v, by
    change IsSelfAdjoint (rankOne ℝ v v)
    rw [ContinuousLinearMap.isSelfAdjoint_iff']; simp⟩

def identitySelf : selfAdjoint (E →L[ℝ] E) := ⟨1, IsSelfAdjoint.one _⟩

theorem rankOne_add_positive_identity (v : E) (ε : ℝ) (hε : 0 < ε) :
    PositiveCone.UniformPositive ((rankOneSelf v + ε • identitySelf).val) := by
  refine ⟨ε, hε, ?_⟩
  intro x
  change ε * ‖x‖ ^ 2 ≤ inner ℝ ((rankOne ℝ v v + ε • (1 : E →L[ℝ] E)) x) x
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, rankOne_apply, inner_add_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg (inner ℝ v x)]

theorem functional_nonneg_rankOne
    (f : selfAdjoint (E →L[ℝ] E) →L[ℝ] ℝ)
    (hpos : ∀ T, PositiveCone.UniformPositive T.val → 0 < f T) (v : E) :
    0 ≤ f (rankOneSelf v) := by
  by_contra h
  have hn : 0 < - f (rankOneSelf v) := neg_pos.mpr (lt_of_not_ge h)
  obtain ⟨ε, hε, hbound⟩ := exists_pos_mul_lt hn (f (identitySelf (E := E)))
  have hp := hpos _ (rankOne_add_positive_identity v ε hε)
  rw [map_add, map_smul] at hp
  simp only [smul_eq_mul] at hp
  nlinarith

/-- A nonzero functional positive on the open positive cone is represented
by a nonzero positive operator. Rank-one perturbations prove positivity. -/
theorem positive_trace_representation
    (f : selfAdjoint (E →L[ℝ] E) →L[ℝ] ℝ) (hf : f ≠ 0)
    (hpos : ∀ T, PositiveCone.UniformPositive T.val → 0 < f T) :
    ∃ Q : E →ₗ[ℝ] E, Q.IsPositive ∧ Q ≠ 0 ∧
      ∀ T : selfAdjoint (E →L[ℝ] E),
        f T = LinearMap.trace ℝ E (Q.comp T.val.toLinearMap) := by
  obtain ⟨Q, hsym, hrepr⟩ := symmetric_trace_representation f
  refine ⟨Q, ?_, ?_, hrepr⟩
  · rw [LinearMap.isPositive_iff]
    refine ⟨hsym, ?_⟩
    intro v
    have h := functional_nonneg_rankOne f hpos v
    rw [hrepr] at h
    change 0 ≤ tracePair Q (rankOne ℝ v v).toLinearMap at h
    simpa only [tracePair_rankOne, real_inner_comm] using h
  · intro hQ
    apply hf
    ext T
    rw [hrepr, hQ]
    simp

/-- Concrete semidefinite separation: no semidefinite duality axiom and
no closedness claim for images of the closed semidefinite cone is used. -/
theorem strict_positive_or_positive_annihilator
    (L : Submodule ℝ (selfAdjoint (E →L[ℝ] E))) :
    (∃ T, T ∈ L ∧ PositiveCone.UniformPositive T.val) ∨
    (∃ Q : E →ₗ[ℝ] E, Q.IsPositive ∧ Q ≠ 0 ∧
      ∀ T ∈ L, LinearMap.trace ℝ E (Q.comp T.val.toLinearMap) = 0) := by
  rcases PositiveCone.strict_positive_or_certificate L with h | ⟨f, hf, hzero, hpos⟩
  · exact Or.inl h
  · obtain ⟨Q, hQ, hn, hr⟩ := positive_trace_representation f hf hpos
    exact Or.inr ⟨Q, hQ, hn, fun T hT => (hr T).symm.trans (hzero T hT)⟩

end LinearStochastic.PositiveDual

namespace LinearStochastic.PositiveDual
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A positive operator with zero trace is zero, including off-diagonal entries. -/
theorem positive_trace_zero_iff (Q : E →ₗ[ℝ] E) (hQ : Q.IsPositive) :
    LinearMap.trace ℝ E Q = 0 ↔ Q = 0 := by
  constructor
  · intro ht
    let b := stdOrthonormalBasis ℝ E
    have htrace := LinearMap.trace_eq_sum_inner Q b
    have hnonneg (i : Fin (Module.finrank ℝ E)) : 0 ≤ inner ℝ (b i) (Q (b i)) := by
      simpa only [real_inner_comm] using hQ.inner_nonneg_left (b i)
    have hzero (i : Fin (Module.finrank ℝ E)) : Q (b i) = 0 := by
      apply (ConeCertificate.positive_quadratic_zero_iff Q hQ (b i)).mp
      have hsum : ∑ j, inner ℝ (b j) (Q (b j)) = 0 := htrace.symm.trans ht
      have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsum i (Finset.mem_univ i)
      simpa only [real_inner_comm] using hz
    apply b.toBasis.ext
    intro i
    exact hzero i
  · rintro rfl
    exact map_zero _
end LinearStochastic.PositiveDual
