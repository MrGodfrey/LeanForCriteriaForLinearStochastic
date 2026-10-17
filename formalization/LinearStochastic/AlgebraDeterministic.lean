module

public import LinearStochastic.AlgebraFlagTransport

@[expose] public section

/-! # The zero-diffusion obstruction flag and the classical Kalman matrix -/
noncomputable section
namespace LinearStochastic.Deterministic
open Module
open scoped BigOperators

section General
variable {𝕜 E U ι : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup U] [Module 𝕜 U] [Fintype ι]
  (A : E →ₗ[𝕜] E) (B : E →ₗ[𝕜] U)

/-- Zero-diffusion coefficients, with A and B in adjoint orientation. -/
def coefficients : AdjointCoefficients (𝕜 := 𝕜) (E := E) (U := U) (ι := ι) :=
  ⟨A, B, fun _ => 0, fun _ => 0⟩

theorem mem_obstruction (S : Submodule 𝕜 E) (v : E) :
    v ∈ (coefficients (ι := ι) A B).obstruction S ↔
      v ∈ S ∧ B v = 0 ∧ A v ∈ S := by
  constructor
  · rintro ⟨hv, _, _, hb, ha⟩
    exact ⟨hv, by simpa [coefficients] using hb, by simpa [coefficients] using ha⟩
  · rintro ⟨hv, hb, ha⟩
    refine ⟨hv, fun _ => 0, fun _ => S.zero_mem, ?_, ?_⟩ <;> simp [coefficients, hb, ha]

/-- The complete flag equals the joint kernels B A^j, j<k, at every stage. -/
theorem mem_flag (k : ℕ) (v : E) :
    v ∈ (coefficients (ι := ι) A B).flag k ↔ ∀ j < k, B ((A^j) v) = 0 := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [AdjointCoefficients.flag_succ, mem_obstruction, ih, ih]
    constructor
    · rintro ⟨_, hB, hA⟩ j hj
      cases j with
      | zero => simpa using hB
      | succ j =>
        have h := hA j (by omega)
        simpa only [pow_succ, Module.End.mul_apply] using h
    · intro h
      refine ⟨fun j hj => h j (by omega), ?_, ?_⟩
      · simpa using h 0 (by omega)
      · intro j hj
        simpa only [pow_succ, Module.End.mul_apply] using h (j+1) (by omega)

theorem flag_eq_kernel_intersection (k : ℕ) :
    (coefficients (ι := ι) A B).flag k = ⨅ j, ⨅ (_ : j < k), (B.comp (A^j)).ker := by
  ext v
  simp only [mem_flag, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]

end General

section Matrices
variable {n r m : ℕ}
  (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)

/-- The genuine horizontal Kalman matrix [B,AB,...,A^(k−1)B]. -/
def kalman (k : ℕ) : Matrix (Fin n) (Fin k × Fin r) ℝ :=
  Coordinates.joint (fun j : Fin k => A^j.val * B)

theorem matrix_mem_flag (k : ℕ) (v : Fin n → ℝ) :
    v ∈ (AdjointCoefficients.fromMatrices A B (fun _ : Fin m => 0) (fun _ => 0)).flag k ↔
      ∀ j < k, (B.transpose * (A.transpose)^j).mulVec v = 0 := by
  have he : AdjointCoefficients.fromMatrices A B (fun _ : Fin m => 0) (fun _ => 0) =
      coefficients (ι := Fin m) A.transpose.toLin' B.transpose.toLin' := by
    simp [AdjointCoefficients.fromMatrices, coefficients]
  rw [he, mem_flag]
  simp only [← Matrix.toLin'_pow, Matrix.toLin'_apply, Matrix.mulVec_mulVec]

/-- The transpose kernel of the literal Kalman matrix is exactly the obstruction flag. -/
theorem kalman_transpose_ker (k : ℕ) :
    (kalman A B k).transpose.mulVecLin.ker =
      (AdjointCoefficients.fromMatrices A B (fun _ : Fin m => 0) (fun _ => 0)).flag k := by
  ext v
  rw [matrix_mem_flag]
  constructor
  · intro hv j hj
    ext a
    have h := congrFun hv (⟨j,hj⟩, a)
    change ((A^j * B).transpose.mulVec v) a = 0 at h
    simpa only [Matrix.transpose_mul, Matrix.transpose_pow, Pi.zero_apply] using h
  · intro hv
    ext p
    rcases p with ⟨j,a⟩
    change ((A^j.val * B).transpose.mulVec v) a = 0
    simpa only [Matrix.transpose_mul, Matrix.transpose_pow, Pi.zero_apply] using congrFun (hv j.val j.isLt) a

/-- Kalman rank is exactly the obstruction codimension at any truncation, including k=0. -/
theorem kalman_rank_codimension (k : ℕ) :
    (kalman A B k).rank = n -
      finrank ℝ ((AdjointCoefficients.fromMatrices A B
        (fun _ : Fin m => 0) (fun _ => 0)).flag k) := by
  rw [← kalman_transpose_ker A B k, ← Matrix.rank_transpose, Matrix.rank]
  have hr := (kalman A B k).transpose.mulVecLin.finrank_range_add_finrank_ker
  have hd : finrank ℝ (Fin n → ℝ) = n := by simp
  omega

/-- In the zero-diffusion case, the prescribed polynomial block-pair rank difference
is exactly the rank of the classical Kalman matrix, with no controllability premise. -/
theorem finitePair_rank_difference_eq_kalman (k : ℕ) :
    let p := Coordinates.finitePair A B (fun _ : Fin m => 0) (fun _ => 0) k
    (Matrix.fromCols p.2 p.1).rank - p.2.rank = (kalman A B (k+1)).rank := by
  dsimp only
  rw [Coordinates.finitePair_rank_codimension, kalman_rank_codimension (m := m)]

#print axioms flag_eq_kernel_intersection
#print axioms kalman_transpose_ker
#print axioms kalman_rank_codimension
end Matrices
end LinearStochastic.Deterministic
