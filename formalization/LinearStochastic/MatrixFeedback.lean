module

public import LinearStochastic.PositiveFinite
public import LinearStochastic.LMIFeedback

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LinearStochastic.MatrixFeedback
open scoped BigOperators InnerProductSpace
open LMIMatrixCoordinates LMIFeedback
variable {n r m : ℕ}

local instance blockNormedSpace {ι : Type*} [Fintype ι] :
    NormedSpace ℝ (ConeBlocks.BlockSpace (EuclideanSpace ℝ (Fin n)) ι) :=
  PiLp.normedSpace 2 ℝ (fun _ : ι => EuclideanSpace ℝ (Fin n))

set_option synthInstance.maxHeartbeats 1000000 in
local instance blockContinuousSMul :
    ContinuousSMul ℝ (ConeBlocks.BlockSpace (EuclideanSpace ℝ (Fin n)) (Option (Fin m))) := by
  change ContinuousSMul ℝ (PiLp 2 (fun _ : Option (Fin m) => EuclideanSpace ℝ (Fin n)))
  infer_instance

/-- The inverse used in the operator proof is the ordinary matrix inverse. -/
theorem inverse_matrix (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef) :
    inverse P.toEuclideanLin (PositiveFinite.matrix_uniformPositive P hP) =
      (P⁻¹).toEuclideanLin := by
  apply LinearMap.ext
  intro x
  apply positive_injective P.toEuclideanLin (PositiveFinite.matrix_uniformPositive P hP)
  rw [apply_inverse]
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M.toEuclideanLin x)
    (Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit))
  simpa only [Matrix.toLpLin_mul_same, Matrix.toLpLin_one, LinearMap.comp_apply,
    LinearMap.id_apply] using h.symm

/-- Literal strict block-matrix positivity supplies the norm margin consumed
by the Hilbert-space proof; there is no extra feasibility assumption. -/
theorem lmi_uniformPositive
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (h : (-matrixLMI A B C D ρ P K).PosDef) :
    PositiveCone.UniformPositive
      (-(LMICoefficients.lmi A.toEuclideanLin B.toEuclideanLin
        (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)
        ρ P.toEuclideanLin K.toEuclideanLin).toContinuousLinearMap) := by
  apply PositiveFinite.blockMatrix_uniformPositive (n := n) (ι := Option (Fin m))
  change (blockMatrix (-LMICoefficients.lmi A.toEuclideanLin B.toEuclideanLin
    (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)
    ρ P.toEuclideanLin K.toEuclideanLin)).PosDef
  rw [map_neg, lmi_coordinate_identity]
  exact h

/-- The feedback is the literal matrix K P⁻¹, with no coordinate surrogate. -/
theorem matrix_closed_loop_quadratic
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (hP : P.PosDef) (h : (-matrixLMI A B C D ρ P K).PosDef)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    2 * inner ℝ ((A + B*(K*P⁻¹)).toEuclideanLin x) ((P⁻¹).toEuclideanLin x) +
      ρ * inner ℝ x ((P⁻¹).toEuclideanLin x) +
      ∑ i, inner ℝ ((C i + D i*(K*P⁻¹)).toEuclideanLin x)
        ((P⁻¹).toEuclideanLin ((C i + D i*(K*P⁻¹)).toEuclideanLin x)) < 0 := by
  have hs : P.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hP.isHermitian
  have hc := closed_loop_lyapunov A.toEuclideanLin B.toEuclideanLin
    (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)
    ρ P.toEuclideanLin hs (PositiveFinite.matrix_uniformPositive P hP) K.toEuclideanLin
    (lmi_uniformPositive A B C D ρ P K h) x hx
  dsimp only at hc
  rw [inverse_matrix P hP] at hc
  simpa only [map_add, Matrix.toLpLin_mul_same, LinearMap.add_apply, LinearMap.comp_apply] using hc

/-- The manuscript closed-loop Lyapunov matrix, in ordinary matrix operations. -/
def lyapunovMatrix (F : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (H : Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) :=
  F.transpose*H + H*F + ρ • H + ∑ i, (N i).transpose*H*N i

theorem lyapunovMatrix_symmetric (F : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsHermitian) (ρ : ℝ) : (lyapunovMatrix F N H ρ).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm] at hH ⊢
  change (lyapunovMatrix F N H ρ).transpose = lyapunovMatrix F N H ρ
  simp only [lyapunovMatrix, Matrix.transpose_add, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.transpose_smul, hH.eq, Matrix.transpose_sum]
  simp only [Matrix.mul_assoc]
  abel

theorem transpose_toEuclideanLin (F : Matrix (Fin n) (Fin n) ℝ) :
    F.transpose.toEuclideanLin = F.toEuclideanLin.adjoint := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.toEuclideanLin_conjTranspose_eq_adjoint F

theorem lyapunovMatrix_quadratic (F : Matrix (Fin n) (Fin n) ℝ)
    (N : Fin m → Matrix (Fin n) (Fin n) ℝ) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsHermitian) (ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((lyapunovMatrix F N H ρ).toEuclideanLin x) x =
      2 * inner ℝ (F.toEuclideanLin x) (H.toEuclideanLin x) +
      ρ * inner ℝ x (H.toEuclideanLin x) +
      ∑ i, inner ℝ ((N i).toEuclideanLin x) (H.toEuclideanLin ((N i).toEuclideanLin x)) := by
  have hs : H.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  simp only [lyapunovMatrix, map_add, map_smul, map_sum, Matrix.toLpLin_mul_same,
    transpose_toEuclideanLin, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, inner_add_left, inner_smul_left,
    conj_trivial, sum_inner, LinearMap.adjoint_inner_left]
  have hfirst : inner ℝ (H.toEuclideanLin x) (F.toEuclideanLin x) =
      inner ℝ (F.toEuclideanLin x) (H.toEuclideanLin x) := real_inner_comm _ _
  have hsecond : inner ℝ (H.toEuclideanLin (F.toEuclideanLin x)) x =
      inner ℝ (F.toEuclideanLin x) (H.toEuclideanLin x) := hs _ _
  have hscalar : inner ℝ (H.toEuclideanLin x) x = inner ℝ x (H.toEuclideanLin x) := real_inner_comm _ _
  have hsum : (∑ i, inner ℝ (H.toEuclideanLin ((N i).toEuclideanLin x)) ((N i).toEuclideanLin x)) =
      ∑ i, inner ℝ ((N i).toEuclideanLin x) (H.toEuclideanLin ((N i).toEuclideanLin x)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact real_inner_comm _ _
  rw [hfirst, hsecond, hscalar, hsum]
  ring

/-- The literal matrix LMI implies the literal negative-definite Lyapunov matrix,
with H=P⁻¹ and feedback K P⁻¹ exactly as in the manuscript. -/
theorem matrix_closed_loop_negative
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)
    (hP : P.PosDef) (h : (-matrixLMI A B C D ρ P K).PosDef) :
    (-lyapunovMatrix (A + B*(K*P⁻¹)) (fun i => C i + D i*(K*P⁻¹)) P⁻¹ ρ).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
    (lyapunovMatrix_symmetric _ _ _ hP.inv.isHermitian ρ).neg
  intro v hv
  let x : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  have hx : x ≠ 0 := by intro hz; exact hv (congrArg WithLp.ofLp hz)
  have hc := matrix_closed_loop_quadratic A B C D ρ P K hP h x hx
  rw [← lyapunovMatrix_quadratic _ _ _ hP.inv.isHermitian] at hc
  have hp : 0 < inner ℝ ((-lyapunovMatrix (A+B*(K*P⁻¹))
      (fun i => C i + D i*(K*P⁻¹)) P⁻¹ ρ).toEuclideanLin x) x := by
    simpa only [map_neg, LinearMap.neg_apply, inner_neg_left, neg_pos] using hc
  simpa only [x, PiLp.inner_apply, Matrix.toLpLin_apply, dotProduct, RCLike.inner_apply, conj_trivial, WithLp.ofLp_toLp, star_trivial, mul_comm] using hp

/-- Original coefficient flag vanishing yields an actual matrix feedback and
an actual positive Lyapunov matrix at every requested rate. -/
theorem arbitrary_rate_matrix_feedback (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) (ρ : ℝ) :
    ∃ (H : Matrix (Fin n) (Fin n) ℝ) (G : Matrix (Fin r) (Fin n) ℝ),
      H.PosDef ∧ (-lyapunovMatrix (A+B*G) (fun i => C i+D i*G) H ρ).PosDef := by
  obtain ⟨P,K,hP,hneg⟩ := arbitrary_rate_positive_matrix_feasible hm A B C D hflag ρ
  exact ⟨P⁻¹,K*P⁻¹,hP.inv,matrix_closed_loop_negative A B C D ρ P K hP hneg⟩

#print axioms arbitrary_rate_matrix_feedback
#print axioms inverse_matrix
#print axioms lmi_uniformPositive
#print axioms matrix_closed_loop_quadratic
#print axioms matrix_closed_loop_negative
end LinearStochastic.MatrixFeedback
