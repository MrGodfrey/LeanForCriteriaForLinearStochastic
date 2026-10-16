import LinearStochastic.LMIFeedback

noncomputable section
namespace LinearStochastic.LMINormalization
open scoped BigOperators InnerProductSpace
open ConeBlocks LMICoefficients
variable {E U ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [Fintype ι] [DecidableEq ι]

/-- The actual normalized LMI inequality -M ≥ I, including symmetry of P. -/
def Feasible (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U) : Prop :=
  P.IsSymmetric ∧ ∀ z : BlockSpace E (Option ι), ‖z‖^2 ≤ inner ℝ (-(lmi A B C D ρ P K z)) z

/-- Genuine homogeneity of the actual LMI turns every strictly feasible pair
into a normalized pair; the scaling is derived from its proved norm margin. -/
theorem normalize_strict
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U)
    (hs : P.IsSymmetric)
    (h : PositiveCone.UniformPositive (-(lmi A B C D ρ P K).toContinuousLinearMap)) :
    ∃ c : ℝ, 0 < c ∧ Feasible A B C D ρ (c • P) (c • K) := by
  obtain ⟨ε,hε,hbound⟩ := h
  refine ⟨ε⁻¹, inv_pos.mpr hε, ?_, ?_⟩
  · intro x y
    simpa only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, conj_trivial]
      using congrArg (fun t : ℝ => ε⁻¹*t) (hs x y)
  · intro z
    rw [lmi_smul, LinearMap.smul_apply, ← smul_neg, inner_smul_left, conj_trivial]
    have hb := hbound z
    change ε * ‖z‖^2 ≤ inner ℝ (-(lmi A B C D ρ P K z)) z at hb
    have hh := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hε.le)
    simpa only [inner_neg_left, ← mul_assoc, inv_mul_cancel₀ hε.ne', one_mul] using hh

/-- The original zero obstruction condition guarantees a nonempty normalized
feasible set at every real rate. -/
theorem feasible_of_zero_flag
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E)
    (hf : (InputStructure.fromForward A B C D).flag (Module.finrank ℝ E) = ⊥) (ρ : ℝ) :
    ∃ P K, Feasible A B C D ρ P K := by
  obtain ⟨P,K,hs,hneg⟩ := arbitrary_rate_feasible A B C D hf ρ
  obtain ⟨c,_,h⟩ := normalize_strict A B C D ρ P K hs hneg
  exact ⟨c • P,c • K,h⟩

/-- The normalized noise principal block yields P ≥ I with no spectral premise. -/
theorem feasible_lyapunov_ge_one [Nonempty ι]
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U)
    (h : Feasible A B C D ρ P K) (x : E) : ‖x‖^2 ≤ inner ℝ (P x) x := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hz := h.2 (inject (some i) x)
  have hi := block_inner (lmi A B C D ρ P K) (some i) (some i) x x
  rw [lmi_noise_diagonal, LinearMap.neg_apply, inner_neg_left] at hi
  simpa only [inner_neg_left, ← hi, neg_neg, inject_norm] using hz

/-- Normalization makes the Lyapunov operator uniformly positive with margin one. -/
theorem feasible_uniformPositive [Nonempty ι]
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U)
    (h : Feasible A B C D ρ P K) : PositiveCone.UniformPositive P.toContinuousLinearMap :=
  ⟨1,zero_lt_one,by
    intro x
    change 1 * ‖x‖^2 ≤ inner ℝ (P x) x
    simpa only [one_mul] using feasible_lyapunov_ge_one A B C D ρ P K h x⟩

/-- The actual inverse of a normalized pair is a contraction in Euclidean norm. -/
theorem feasible_inverse_bound [Nonempty ι]
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U)
    (h : Feasible A B C D ρ P K) (x : E) :
    ‖LMIFeedback.inverse P (feasible_uniformPositive A B C D ρ P K h) x‖ ≤ ‖x‖ := by
  let H := LMIFeedback.inverse P (feasible_uniformPositive A B C D ρ P K h)
  have hsq := feasible_lyapunov_ge_one A B C D ρ P K h (H x)
  have hPH : P (H x) = x := LMIFeedback.apply_inverse _ _ _
  rw [hPH] at hsq
  have hc := real_inner_le_norm (x) (H x)
  change ‖H x‖ ≤ ‖x‖
  nlinarith [norm_nonneg (H x),norm_nonneg x]

theorem feasible_inverse_norm_le_one [Nonempty ι]
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U)
    (h : Feasible A B C D ρ P K) :
    ‖(LMIFeedback.inverse P (feasible_uniformPositive A B C D ρ P K h)).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖LMIFeedback.inverse P (feasible_uniformPositive A B C D ρ P K h) x‖ ≤ 1*‖x‖
  simpa only [one_mul] using feasible_inverse_bound A B C D ρ P K h x

#print axioms feasible_inverse_norm_le_one
#print axioms normalize_strict
#print axioms feasible_of_zero_flag
#print axioms feasible_lyapunov_ge_one
end LinearStochastic.LMINormalization
