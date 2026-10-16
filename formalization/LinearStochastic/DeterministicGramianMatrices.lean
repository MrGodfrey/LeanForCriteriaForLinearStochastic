import LinearStochastic.DeterministicGramianControl
import LinearStochastic.ZeroObservationMatrices

/-! The positive exponential Gramian is derived from the paper's literal
finite Kalman rank condition, closing the algebra-to-analytic hypothesis. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.DeterministicGramianMatrices
open Module
open ZeroObservationMatrices
variable {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)

/-- Full rank of [B,AB,...,A^{n−1}B] implies the actual Euclidean-adjoint
power-kernel condition used in the Gramian theorem. -/
theorem observable_of_kalman_rank (hK : (Deterministic.kalman A B n).rank = n) :
    ∀ v : EuclideanSpace ℝ (Fin n),
      (∀ k : ℕ, (matrixMap B).adjoint (((matrixMap A).adjoint^k) v) = 0) → v=0 := by
  have hf : (AdjointCoefficients.fromMatrices A B (fun _ : Fin 1 => 0) (fun _ => 0)).flag n = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have hd := Deterministic.kalman_rank_codimension (m:=1) A B n
    have hb := Submodule.finrank_le ((AdjointCoefficients.fromMatrices A B
      (fun _ : Fin 1 => 0) (fun _ => 0)).flag n)
    simp only [Module.finrank_pi,Fintype.card_fin] at hb
    rw [hK] at hd
    omega
  have he := (matrix_flag_bot_iff A B (fun _ : Fin 1 => 0) (fun _ => 0) n).mp hf
  have hz : ZeroObservationFlag.coefficients (matrixMap A) (matrixMap B)
      (fun _ : Fin 1 => matrixMap (0 : Matrix (Fin n) (Fin n) ℝ))
      (fun _ => matrixMap (0 : Matrix (Fin n) (Fin r) ℝ)) =
      Deterministic.coefficients (ι:=Fin 1) (matrixMap A).adjoint.toLinearMap (matrixMap B).adjoint.toLinearMap := by
    simp only [ZeroObservationFlag.coefficients,Deterministic.coefficients,matrixMap,map_zero]
    rfl
  rw [hz] at he
  intro v hv
  have hp (k : ℕ) : (((matrixMap A).adjoint.toLinearMap^k) v) = (((matrixMap A).adjoint^k) v) := by
    induction k with
    | zero => rfl
    | succ k ih => simpa only [pow_succ',Module.End.mul_apply,mul_apply_eq_comp,ContinuousLinearMap.coe_coe] using congrArg (matrixMap A).adjoint ih
  have hm : v ∈ (Deterministic.coefficients (ι:=Fin 1)
      (matrixMap A).adjoint.toLinearMap (matrixMap B).adjoint.toLinearMap).flag n := by
    apply (Deterministic.mem_flag _ _ n v).mpr
    intro k _
    change (matrixMap B).adjoint (((matrixMap A).adjoint.toLinearMap^k) v) = 0
    rw [hp]
    exact hv k
  rwa [he,Submodule.mem_bot] at hm

/-- In particular the actual integrated Gramian is positive on every nonzero
state whenever the manuscript's finite Kalman matrix has full rank. -/
theorem gramian_positive (hK : (Deterministic.kalman A B n).rank = n)
    (h : ℝ) (hh : 0 < h) (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) :
    0 < inner ℝ v (DeterministicGramian.gramian (matrixMap A) (matrixMap B) h v) :=
  DeterministicGramian.quadratic_pos (matrixMap A) (matrixMap B) h hh (observable_of_kalman_rank A B hK) v hv

/-- The literal matrix Kalman test therefore supplies the genuine exact
endpoint Gramian control kernel, not an assumed invertibility oracle. -/
theorem terminal_integral (hK : (Deterministic.kalman A B n).rank = n)
    (h : ℝ) (hh : 0 < h) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ t in Set.Icc 0 h, (NormedSpace.exp ((h-t) • matrixMap A))
      (matrixMap B (DeterministicGramianControl.kernel (matrixMap A) (matrixMap B) h hh
        (observable_of_kalman_rank A B hK) t v))) = v :=
  DeterministicGramianControl.terminal_integral (matrixMap A) (matrixMap B) h hh
    (observable_of_kalman_rank A B hK) v

end LinearStochastic.DeterministicGramianMatrices
