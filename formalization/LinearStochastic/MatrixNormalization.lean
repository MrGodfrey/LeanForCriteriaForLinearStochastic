module

public import LinearStochastic.LMINormalization
public import LinearStochastic.MatrixFeedback
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LinearStochastic.MatrixNormalization
open scoped BigOperators InnerProductSpace
open LMIMatrixCoordinates
variable {n r m : ℕ}

local instance blockNormedSpace {ι : Type*} [Fintype ι] :
    NormedSpace ℝ (ConeBlocks.BlockSpace (EuclideanSpace ℝ (Fin n)) ι) :=
  PiLp.normedSpace 2 ℝ (fun _ : ι => EuclideanSpace ℝ (Fin n))
set_option synthInstance.maxHeartbeats 1000000 in
local instance blockContinuousSMul :
    ContinuousSMul ℝ (ConeBlocks.BlockSpace (EuclideanSpace ℝ (Fin n)) (Option (Fin m))) := by
  change ContinuousSMul ℝ (PiLp 2 (fun _ : Option (Fin m) => EuclideanSpace ℝ (Fin n)))
  infer_instance

/-- Literal normalized matrix feasible set from the manuscript. -/
def Feasible (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ) : Prop :=
  P.IsSymm ∧ (-matrixLMI A B C D ρ P K - 1).PosSemidef

theorem blockMatrix_id {ι : Type*} [Fintype ι] [DecidableEq ι] :
    blockMatrix (LinearMap.id : ConeBlocks.BlockSpace (EuclideanSpace ℝ (Fin n)) ι →ₗ[ℝ] _) = 1 := by
  apply Matrix.toEuclideanLin.injective
  ext x
  simp only [blockMatrix_action, LinearMap.id_apply, LinearIsometryEquiv.apply_symm_apply,
    Matrix.toLpLin_one]

theorem blockMatrix_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : ConeBlocks.BlockSpace (EuclideanSpace ℝ (Fin n)) ι →ₗ[ℝ] _)
    (hL : L.IsPositive) : (blockMatrix L).PosSemidef := by
  apply Matrix.isPositive_toEuclideanLin_iff.mp
  change (Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm (flattenEnd L))).IsPositive
  rw [LinearEquiv.apply_symm_apply]
  exact (LinearMap.isPositive_linearIsometryEquiv_conj_iff (𝕜 := ℝ) (T := L)
    (flatten (n := n) (ι := ι))).mpr hL

theorem feasible_of_operator
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (h : LMINormalization.Feasible A.toEuclideanLin B.toEuclideanLin
      (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)
      ρ P.toEuclideanLin K.toEuclideanLin) : Feasible A B C D ρ P K := by
  refine ⟨Matrix.isHermitian_iff_isSymm.mp (Matrix.isSymmetric_toEuclideanLin_iff.mp h.1), ?_⟩
  let L := LMICoefficients.lmi A.toEuclideanLin B.toEuclideanLin
    (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)
    ρ P.toEuclideanLin K.toEuclideanLin
  have hs : L.IsSymmetric := LMICoefficients.lmi_symmetric _ _ _ _ _ _ h.1 _
  have hp : (-L - LinearMap.id).IsPositive := by
    refine ⟨?_, ?_⟩
    · intro x y
      simpa only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply,
        inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right] using
        congrArg (fun t : ℝ => -t - inner ℝ x y) (hs x y)
    · intro z
      have hz := h.2 z
      change 0 ≤ inner ℝ (-(L z) - z) z
      simpa only [LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply,
        inner_sub_left, real_inner_self_eq_norm_sq, sub_nonneg] using hz
  have hx := blockMatrix_posSemidef (-L - LinearMap.id) hp
  simpa only [map_sub, map_neg, blockMatrix_id, L, lmi_coordinate_identity] using hx

/-- Actual matrix feasible pairs normalize by a derived positive scalar. -/
theorem normalize_strict
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (hs : P.IsSymm) (hp : (-matrixLMI A B C D ρ P K).PosDef) :
    ∃ c : ℝ, 0 < c ∧ Feasible A B C D ρ (c • P) (c • K) := by
  obtain ⟨c,hc,h⟩ := LMINormalization.normalize_strict A.toEuclideanLin B.toEuclideanLin
    (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)
    ρ P.toEuclideanLin K.toEuclideanLin
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hs))
    (MatrixFeedback.lmi_uniformPositive A B C D ρ P K hp)
  exact ⟨c,hc,feasible_of_operator A B C D ρ (c•P) (c•K) (by simpa using h)⟩

theorem feasible_of_zero_flag
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) (ρ : ℝ) :
    ∃ P K, Feasible A B C D ρ P K := by
  obtain ⟨P,K,hs,hp⟩ := arbitrary_rate_matrix_feasible A B C D hflag ρ
  obtain ⟨c,_,h⟩ := normalize_strict A B C D ρ P K hs hp
  exact ⟨c•P,c•K,h⟩

/-- Every noise principal block enforces the literal matrix inequality P ≥ I. -/
theorem feasible_ge_one
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (h : Feasible A B C D ρ P K) (i : Fin m) : (P - 1).PosSemidef := by
  have hp := h.2.submatrix (fun a : Fin n => (some i,a))
  have he : (-matrixLMI A B C D ρ P K - 1).submatrix
      (fun a : Fin n => (some i,a)) (fun a : Fin n => (some i,a)) = P-1 := by
    ext a b
    simp [Matrix.submatrix, Matrix.one_apply]
  rwa [he] at hp

theorem feasible_posDef
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (h : Feasible A B C D ρ P K) (i : Fin m) : P.PosDef := by
  have hp := (Matrix.PosDef.one (n := Fin n) (R := ℝ)).add_posSemidef
    (feasible_ge_one A B C D ρ P K h i)
  convert hp using 1
  abel

theorem feasible_strict_lmi
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (h : Feasible A B C D ρ P K) : (-matrixLMI A B C D ρ P K).PosDef := by
  have hp := Matrix.PosDef.one.add_posSemidef h.2
  convert hp using 1
  abel

/-- The inverse in the normalized matrix statement is the ordinary nonsingular
inverse and is a contraction for the Euclidean norm. -/
theorem feasible_inverse_bound
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (h : Feasible A B C D ρ P K) (i : Fin m) (x : EuclideanSpace ℝ (Fin n)) :
    ‖(P⁻¹).toEuclideanLin x‖ ≤ ‖x‖ := by
  have hp := feasible_posDef A B C D ρ P K h i
  have hps := (Matrix.isPositive_toEuclideanLin_iff.mpr
    (feasible_ge_one A B C D ρ P K h i)).2 ((P⁻¹).toEuclideanLin x)
  have hinv : P.toEuclideanLin ((P⁻¹).toEuclideanLin x) = x := by
    rw [← MatrixFeedback.inverse_matrix P hp, LMIFeedback.apply_inverse]
  change 0 ≤ inner ℝ ((P-1).toEuclideanLin ((P⁻¹).toEuclideanLin x)) ((P⁻¹).toEuclideanLin x) at hps
  simp only [map_sub,Matrix.toLpLin_one,LinearMap.sub_apply,LinearMap.id_apply,
    inner_sub_left,real_inner_self_eq_norm_sq,hinv] at hps
  have hc := real_inner_le_norm x ((P⁻¹).toEuclideanLin x)
  nlinarith [norm_nonneg ((P⁻¹).toEuclideanLin x),norm_nonneg x]

theorem feasible_inverse_norm_le_one
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (h : Feasible A B C D ρ P K) (i : Fin m) :
    ‖(P⁻¹).toEuclideanLin.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  change ‖(P⁻¹).toEuclideanLin x‖ ≤ 1 * ‖x‖
  simpa only [one_mul] using feasible_inverse_bound A B C D ρ P K h i x

#print axioms feasible_inverse_norm_le_one
#print axioms feasible_strict_lmi
#print axioms feasible_of_zero_flag
#print axioms feasible_ge_one
end LinearStochastic.MatrixNormalization
