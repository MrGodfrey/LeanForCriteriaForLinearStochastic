module

public import LinearStochastic.MatrixMinimum

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LinearStochastic.LMIStability
open scoped BigOperators InnerProductSpace
open ConeBlocks LMICoefficients
variable {E U ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [Fintype ι] [DecidableEq ι]

local instance genericBlockNormedSpace {κ : Type*} [Fintype κ] :
    NormedSpace ℝ (BlockSpace E κ) := PiLp.normedSpace 2 ℝ (fun _ : κ => E)

/-- Exact affine dependence of the actual block LMI on the requested rate. -/
theorem lmi_rate_difference
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ σ : ℝ) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U) :
    lmi A B C D σ P K = lmi A B C D ρ P K +
      (σ-ρ) • liftBlock (ι := Option ι) none none P := by
  simp only [lmi,liftBlock_add,liftBlock_smul,sub_smul]
  abel

theorem lmi_rate_continuous
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U) :
    Continuous (fun ρ : ℝ => (lmi A B C D ρ P K).toContinuousLinearMap) := by
  have he : (fun ρ : ℝ => (lmi A B C D ρ P K).toContinuousLinearMap) =
      fun ρ => (lmi A B C D 0 P K).toContinuousLinearMap +
        ρ • (liftBlock (ι := Option ι) none none P).toContinuousLinearMap := by
    funext ρ
    rw [lmi_rate_difference A B C D 0 ρ P K]
    simp only [sub_zero,map_add,map_smul]
  rw [he]
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- Every dilation c>1 of a normalized pair has a genuine positive margin. -/
theorem scaled_margin
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U)
    (h : LMINormalization.Feasible A B C D ρ P K) (c : ℝ) (hc : 1 < c) :
    PositiveCone.UniformPositive
      (-(lmi A B C D ρ (c•P) (c•K)).toContinuousLinearMap -
        ContinuousLinearMap.id ℝ (BlockSpace E (Option ι))) := by
  refine ⟨c-1,sub_pos.mpr hc,fun z => ?_⟩
  have hz := mul_le_mul_of_nonneg_left (h.2 z) (le_trans zero_le_one hc.le)
  change (c-1)*‖z‖^2 ≤ inner ℝ (-(lmi A B C D ρ (c•P) (c•K) z)-z) z
  rw [lmi_smul,LinearMap.smul_apply,←smul_neg,inner_sub_left,
    inner_smul_left,conj_trivial,real_inner_self_eq_norm_sq]
  nlinarith

/-- The same scaled pair remains normalized feasible at every sufficiently
nearby rate, by actual operator-norm continuity and the positive margin. -/
theorem scaled_feasible_near
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U)
    (h : LMINormalization.Feasible A B C D ρ P K) (c : ℝ) (hc : 1 < c) :
    ∀ᶠ σ in nhds ρ, LMINormalization.Feasible A B C D σ (c•P) (c•K) := by
  let T : ℝ → BlockSpace E (Option ι) →L[ℝ] BlockSpace E (Option ι) :=
    fun σ => -(lmi A B C D σ (c•P) (c•K)).toContinuousLinearMap - ContinuousLinearMap.id ℝ _
  have hT : Continuous T := (lmi_rate_continuous A B C D (c•P) (c•K)).neg.sub continuous_const
  obtain ⟨ε,hε,hbound⟩ := scaled_margin A B C D ρ P K h c hc
  have hnear : ∀ᶠ σ in nhds ρ, ‖T σ-T ρ‖ < ε := by
    have he : ‖T ρ-T ρ‖ < ε := by simpa only [sub_self,norm_zero] using hε
    have hd : Continuous (fun σ => T σ-T ρ) := hT.sub continuous_const
    exact hd.norm.continuousAt.eventually_lt_const he
  filter_upwards [hnear] with σ hσ
  have hp := PositiveCone.uniformPositive_of_norm_sub_lt (T ρ) (T σ) ε hε hbound hσ
  refine ⟨?_,fun z => ?_⟩
  · intro x y
    simpa only [LinearMap.smul_apply,inner_smul_left,inner_smul_right,conj_trivial]
      using congrArg (fun t : ℝ => c*t) (h.1 x y)
  · obtain ⟨δ,hδ,hd⟩ := hp
    have hz := hd z
    change δ * ‖z‖^2 ≤ inner ℝ (-(lmi A B C D σ (c•P) (c•K) z)-z) z at hz
    rw [inner_sub_left,real_inner_self_eq_norm_sq] at hz
    nlinarith [sq_nonneg ‖z‖]

end LinearStochastic.LMIStability

namespace LinearStochastic.MatrixStability
open scoped InnerProductSpace
open LMIMatrixCoordinates MatrixNormalization
variable {n r m : ℕ}

local instance blockNormedSpace {ι : Type*} [Fintype ι] :
    NormedSpace ℝ (ConeBlocks.BlockSpace (EuclideanSpace ℝ (Fin n)) ι) :=
  PiLp.normedSpace 2 ℝ (fun _ : ι => EuclideanSpace ℝ (Fin n))
set_option synthInstance.maxHeartbeats 1000000 in
local instance blockContinuousSMul :
    ContinuousSMul ℝ (ConeBlocks.BlockSpace (EuclideanSpace ℝ (Fin n)) (Option (Fin m))) := by
  change ContinuousSMul ℝ (PiLp 2 (fun _ : Option (Fin m) => EuclideanSpace ℝ (Fin n)))
  infer_instance

/-- Reverse direction of the normalized operator/matrix correspondence. -/
theorem operator_of_feasible
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (h : Feasible A B C D ρ P K) :
    LMINormalization.Feasible A.toEuclideanLin B.toEuclideanLin
      (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)
      ρ P.toEuclideanLin K.toEuclideanLin := by
  refine ⟨Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr h.1),?_⟩
  intro z
  let L := LMICoefficients.lmi A.toEuclideanLin B.toEuclideanLin
    (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)
    ρ P.toEuclideanLin K.toEuclideanLin
  have he : blockMatrix (-L-LinearMap.id) = -matrixLMI A B C D ρ P K - 1 := by
    simp only [map_sub,map_neg,blockMatrix_id,L,lmi_coordinate_identity]
  have hp := h.2
  rw [← he] at hp
  have hz := (Matrix.isPositive_toEuclideanLin_iff.mpr hp).2 (flatten z)
  change 0 ≤ inner ℝ ((blockMatrix (-L-LinearMap.id)).toEuclideanLin (flatten z)) (flatten z) at hz
  rw [blockMatrix_action,LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.inner_map_map] at hz
  simpa only [LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.id_apply,
    inner_sub_left,real_inner_self_eq_norm_sq,sub_nonneg] using hz

theorem scaled_feasible_near
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (h : Feasible A B C D ρ P K) (c : ℝ) (hc : 1 < c) :
    ∀ᶠ σ in nhds ρ, Feasible A B C D σ (c•P) (c•K) := by
  have hf := LMIStability.scaled_feasible_near A.toEuclideanLin B.toEuclideanLin
    (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)
    ρ P.toEuclideanLin K.toEuclideanLin (operator_of_feasible A B C D ρ P K h) c hc
  filter_upwards [hf] with σ hσ
  exact feasible_of_operator A B C D σ (c•P) (c•K) (by simpa using hσ)

#print axioms scaled_feasible_near
end LinearStochastic.MatrixStability
