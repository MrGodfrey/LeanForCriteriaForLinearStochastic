module

public import LinearStochastic.AlgebraWords
public import LinearStochastic.InputStructure

@[expose] public section

/-!
# Algebraic reduction with injective joint adjoint diffusion

The only additional algebraic datum is an actual left inverse of the stacked
adjoint diffusion map. The fixed-space and word-space conclusions are proved.
-/
noncomputable section
namespace LinearStochastic.SurjectiveReduction
open Module
open scoped BigOperators

section Algebra
variable {𝕜 E U ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AddCommGroup U] [Module 𝕜 U] [Fintype ι]
variable (s : AdjointCoefficients (𝕜 := 𝕜) (E := E) (U := U) (ι := ι))

/-- Sum of the channel observation terms. -/
def jointObservation : (ι → E) →ₗ[𝕜] U := ∑ i, (s.D i).comp (LinearMap.proj i)

/-- Sum of the channel drift terms. -/
def jointDrift : (ι → E) →ₗ[𝕜] E := ∑ i, (s.C i).comp (LinearMap.proj i)

variable (L : U →ₗ[𝕜] (ι → E))

def feedback : E →ₗ[𝕜] (ι → E) := L.comp s.B
def reducedObservation : E →ₗ[𝕜] U := s.B - (jointObservation s).comp (feedback s L)
def reducedDrift : E →ₗ[𝕜] E := s.A - (jointDrift s).comp (feedback s L)

/-- Channel maps and the drift map, i.e. Eᵢ† and F† in the manuscript. -/
def generators : Option ι → E →ₗ[𝕜] E
  | none => reducedDrift s L
  | some i => (LinearMap.proj i).comp (feedback s L)

/-- Zero observation uniquely fixes all martingale coefficients. -/
theorem observation_iff (hL : L.comp (jointObservation s) = LinearMap.id)
    (v : E) (w : ι → E) :
    s.B v + jointObservation s w = 0 ↔
      reducedObservation s L v = 0 ∧ w = -(feedback s L v) := by
  have hl (a : ι → E) : L (jointObservation s a) = a := LinearMap.congr_fun hL a
  constructor
  · intro h
    have ht := congrArg L h
    simp only [map_add, map_zero, hl] at ht
    have hw : w = -(feedback s L v) := eq_neg_of_add_eq_zero_right ht
    refine ⟨?_, hw⟩
    rw [hw] at h
    simpa only [reducedObservation, LinearMap.sub_apply, LinearMap.comp_apply,
      map_neg, sub_eq_add_neg, LinearMap.add_apply, LinearMap.neg_apply] using h
  · rintro ⟨h, rfl⟩
    simpa only [reducedObservation, LinearMap.sub_apply, LinearMap.comp_apply,
      map_neg, sub_eq_add_neg, LinearMap.add_apply, LinearMap.neg_apply] using h

/-- Pointwise elimination retains every constraint of the original obstruction. -/
theorem mem_obstruction_iff (hL : L.comp (jointObservation s) = LinearMap.id)
    (V : Submodule 𝕜 E) (v : E) :
    v ∈ s.obstruction V ↔ v ∈ V ∧ reducedObservation s L v = 0 ∧
      (∀ i, feedback s L v i ∈ V) ∧ reducedDrift s L v ∈ V := by
  have hJ (w : ι → E) : jointObservation s w = ∑ i, s.D i (w i) := by
    simp [jointObservation, LinearMap.sum_apply]
  have hC (w : ι → E) : jointDrift s w = ∑ i, s.C i (w i) := by
    simp [jointDrift, LinearMap.sum_apply]
  constructor
  · rintro ⟨hv, w, hw, hB, hA⟩
    rw [← hJ] at hB
    obtain ⟨hObs, hW⟩ := (observation_iff s L hL v w).mp hB
    refine ⟨hv, hObs, ?_, ?_⟩
    · intro i
      have hi := hw i
      rw [hW] at hi
      exact V.neg_mem_iff.mp hi
    · rw [← hC, hW] at hA
      simpa only [reducedDrift, LinearMap.sub_apply, LinearMap.comp_apply,
        map_neg, sub_eq_add_neg, LinearMap.add_apply, LinearMap.neg_apply] using hA
  · rintro ⟨hv, hObs, hw, hA⟩
    refine ⟨hv, -(feedback s L v), fun i => V.neg_mem (hw i), ?_, ?_⟩
    · rw [← hJ]
      exact (observation_iff s L hL v _).mpr ⟨hObs, rfl⟩
    · rw [← hC]
      simpa only [reducedDrift, LinearMap.sub_apply, LinearMap.comp_apply,
        map_neg, sub_eq_add_neg, LinearMap.add_apply, LinearMap.neg_apply] using hA

/-- A fixed obstruction is exactly a common invariant subspace inside the reduced kernel. -/
theorem fixed_iff (hL : L.comp (jointObservation s) = LinearMap.id)
    (V : Submodule 𝕜 E) :
    s.obstruction V = V ↔
      V ≤ (reducedObservation s L).ker ∧ Words.Invariant (generators s L) V := by
  constructor
  · intro h
    have hp (v : E) (hv : v ∈ V) :=
      (mem_obstruction_iff s L hL V v).mp (h.symm ▸ hv)
    refine ⟨fun v hv => (hp v hv).2.1, ?_⟩
    intro i x hx
    obtain ⟨v, hv, rfl⟩ := hx
    cases i with
    | some i => exact (hp v hv).2.2.1 i
    | none => exact (hp v hv).2.2.2
  · rintro ⟨hObs, hInv⟩
    apply le_antisymm (s.obstruction_le V)
    intro v hv
    apply (mem_obstruction_iff s L hL V v).mpr
    exact ⟨hv, hObs hv, fun i => hInv (some i) ⟨v, hv, rfl⟩,
      hInv none ⟨v, hv, rfl⟩⟩
end Algebra

section Orthogonal
variable {E U ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [Fintype ι]
variable (s : AdjointCoefficients (𝕜 := ℝ) (E := E) (U := U) (ι := ι))
  (L : U →ₗ[ℝ] (ι → E))

/-- The stabilized obstruction equals the annihilator of the finite reduced word span. -/
theorem flag_eq_orthogonal_wordSpan
    (hL : L.comp (jointObservation s) = LinearMap.id) :
    s.flag (finrank ℝ E) =
      (Words.wordSpan (fun i => (generators s L i).adjoint)
        (reducedObservation s L).adjoint.range (finrank ℝ E - 1))ᗮ := by
  have hf := (fixed_iff s L hL (s.flag (finrank ℝ E))).mp s.flag_stable_at_finrank
  have hg := Words.orthogonal_wordRange_greatest
    (fun i => (generators s L i).adjoint) (reducedObservation s L).adjoint
  simp only [LinearMap.adjoint_adjoint] at hg
  apply le_antisymm
  · exact hg.2.2 _ hf.2 hf.1
  · exact s.fixed_le_flag
      ((fixed_iff s L hL _).mpr ⟨hg.2.1, hg.1⟩).ge _

/-- Vanishing of the obstruction is equivalent to fullness of this finite word span. -/
theorem flag_bot_iff_wordSpan_top
    (hL : L.comp (jointObservation s) = LinearMap.id) :
    s.flag (finrank ℝ E) = ⊥ ↔
      Words.wordSpan (fun i => (generators s L i).adjoint)
        (reducedObservation s L).adjoint.range (finrank ℝ E - 1) = ⊤ := by
  rw [flag_eq_orthogonal_wordSpan s L hL, Submodule.orthogonal_eq_bot_iff]

#print axioms flag_eq_orthogonal_wordSpan
end Orthogonal
end LinearStochastic.SurjectiveReduction

namespace LinearStochastic.SurjectiveReduction
open Module
open scoped BigOperators
variable {E U ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [Fintype ι]

/-- Coordinate projection from the Hilbert direct sum of noise channels. -/
def channelProjection (i : ι) : PiLp 2 (fun _ : ι => E) →ₗ[ℝ] E :=
  (LinearMap.proj i).comp (WithLp.linearEquiv 2 ℝ (ι → E)).toLinearMap

/-- The canonical noise-channel inclusion. -/
def channelInjection (i : ι) : E →ₗ[ℝ] PiLp 2 (fun _ : ι => E) :=
  (channelProjection (E := E) i).adjoint

/-- L is J† expressed in ordinary channel-product coordinates. -/
def canonicalLeftInverse (D : ι → U →ₗ[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion D)) : U →ₗ[ℝ] (ι → E) :=
  (WithLp.linearEquiv 2 ℝ (ι → E)).toLinearMap.comp
    (InputStructure.canonicalRightInverse (InputStructure.jointDiffusion D) hD).adjoint

/-- Identification of the actual stacked observation, proved channel by channel. -/
theorem jointObservation_fromForward (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (C : ι → E →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E) (w : ι → E) :
    jointObservation (InputStructure.fromForward A B C D) w =
      (InputStructure.jointDiffusion D).adjoint (WithLp.toLp 2 w) := by
  rw [InputStructure.jointDiffusion_adjoint_apply]
  simp [jointObservation, InputStructure.fromForward, LinearMap.sum_apply]

theorem jointDrift_fromForward (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (C : ι → E →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E) (w : ι → E) :
    jointDrift (InputStructure.fromForward A B C D) w =
      (InputStructure.jointDiffusion C).adjoint (WithLp.toLp 2 w) := by
  rw [InputStructure.jointDiffusion_adjoint_apply]
  simp [jointDrift, InputStructure.fromForward, LinearMap.sum_apply]

/-- No inverse is postulated: the Gram inverse in InputStructure constructs this left inverse. -/
theorem canonicalLeftInverse_left_inverse (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (C : ι → E →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion D)) :
    (canonicalLeftInverse D hD).comp (jointObservation (InputStructure.fromForward A B C D)) =
      LinearMap.id := by
  let J := InputStructure.canonicalRightInverse (InputStructure.jointDiffusion D) hD
  have hJ : J.adjoint.comp (InputStructure.jointDiffusion D).adjoint = LinearMap.id := by
    have ht := congrArg LinearMap.adjoint
      (InputStructure.canonicalRightInverse_right_inverse (InputStructure.jointDiffusion D) hD)
    simpa only [LinearMap.adjoint_comp, LinearMap.adjoint_id] using ht
  ext w i
  have hw := LinearMap.congr_fun hJ (WithLp.toLp 2 w)
  change J.adjoint ((InputStructure.jointDiffusion D).adjoint (WithLp.toLp 2 w)) =
    WithLp.toLp 2 w at hw
  change (J.adjoint (jointObservation (InputStructure.fromForward A B C D) w)) i = w i
  rw [jointObservation_fromForward, hw]

/-- The paper's H=B(I−JD). -/
def forwardH (B : U →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion D)) : U →ₗ[ℝ] E :=
  B.comp (LinearMap.id -
    (InputStructure.canonicalRightInverse (InputStructure.jointDiffusion D) hD).comp
      (InputStructure.jointDiffusion D))

/-- The paper's F=A−BJC. -/
def forwardF (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (C : ι → E →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion D)) : E →ₗ[ℝ] E :=
  A - B.comp ((InputStructure.canonicalRightInverse (InputStructure.jointDiffusion D) hD).comp
    (InputStructure.jointDiffusion C))

/-- The paper's Eᵢ=BJᵢ, with Jᵢ the ith block of the constructed J. -/
def forwardE (B : U →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion D)) (i : ι) : E →ₗ[ℝ] E :=
  B.comp ((InputStructure.canonicalRightInverse (InputStructure.jointDiffusion D) hD).comp
    (channelInjection i))

def forwardGenerators (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (C : ι → E →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion D)) : Option ι → E →ₗ[ℝ] E
  | none => forwardF A B C D hD
  | some i => forwardE B D hD i

/-- Identification of the reduced observation with the genuine forward H adjoint. -/
theorem reducedObservation_eq_H_adjoint (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (C : ι → E →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion D)) :
    reducedObservation (InputStructure.fromForward A B C D) (canonicalLeftInverse D hD) =
      (forwardH B D hD).adjoint := by
  ext v
  simp only [reducedObservation, LinearMap.sub_apply, LinearMap.comp_apply,
    jointObservation_fromForward, forwardH, LinearMap.adjoint_comp, map_sub,
    LinearMap.adjoint_id]
  rfl

/-- Identification of the reduced drift with the genuine forward F adjoint. -/
theorem reducedDrift_eq_F_adjoint (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (C : ι → E →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion D)) :
    reducedDrift (InputStructure.fromForward A B C D) (canonicalLeftInverse D hD) =
      (forwardF A B C D hD).adjoint := by
  ext v
  simp only [reducedDrift, LinearMap.sub_apply, LinearMap.comp_apply,
    jointDrift_fromForward, forwardF, map_sub, LinearMap.adjoint_comp]
  rfl

/-- Every reduced channel map is the adjoint of its stated original-coefficient Eᵢ. -/
theorem generators_eq_forward_adjoint (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (C : ι → E →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion D)) (i : Option ι) :
    generators (InputStructure.fromForward A B C D) (canonicalLeftInverse D hD) i =
      (forwardGenerators A B C D hD i).adjoint := by
  cases i with
  | none => exact reducedDrift_eq_F_adjoint A B C D hD
  | some i =>
    simp only [generators, forwardGenerators, forwardE, channelInjection,
      LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
    rfl

/-- The full original-coefficient algebraic identity used in prop:exact-rank.
Its only additional premise is surjectivity of the actual joint diffusion map. -/
theorem canonical_flag_eq_orthogonal_words (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (C : ι → E →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion D)) :
    (InputStructure.fromForward A B C D).flag (finrank ℝ E) =
      (Words.wordSpan (forwardGenerators A B C D hD)
        (forwardH B D hD).range (finrank ℝ E - 1))ᗮ := by
  have ht := flag_eq_orthogonal_wordSpan (InputStructure.fromForward A B C D)
    (canonicalLeftInverse D hD) (canonicalLeftInverse_left_inverse A B C D hD)
  simpa only [generators_eq_forward_adjoint, reducedObservation_eq_H_adjoint,
    LinearMap.adjoint_adjoint] using ht

/-- Exact finite-dimensional rank obstruction in the original forward coefficients. -/
theorem canonical_flag_bot_iff (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (C : ι → E →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E)
    (hD : Function.Surjective (InputStructure.jointDiffusion D)) :
    (InputStructure.fromForward A B C D).flag (finrank ℝ E) = ⊥ ↔
      Words.wordSpan (forwardGenerators A B C D hD)
        (forwardH B D hD).range (finrank ℝ E - 1) = ⊤ := by
  rw [canonical_flag_eq_orthogonal_words A B C D hD, Submodule.orthogonal_eq_bot_iff]

#print axioms canonical_flag_eq_orthogonal_words
end LinearStochastic.SurjectiveReduction
