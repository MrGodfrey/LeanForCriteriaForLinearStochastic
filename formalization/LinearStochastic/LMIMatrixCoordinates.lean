import LinearStochastic.LMICoefficients
import LinearStochastic.AlgebraFlagTransport

noncomputable section
namespace LinearStochastic.LMIMatrixCoordinates
open scoped BigOperators InnerProductSpace
open ConeBlocks
variable {n r m : ℕ}

section Flatten
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Standard channel-first curry/uncurry coordinates, preserving every state coordinate. -/
def flattenLinear : BlockSpace (EuclideanSpace ℝ (Fin n)) ι ≃ₗ[ℝ]
    EuclideanSpace ℝ (ι × Fin n) where
  toFun x := WithLp.toLp 2 (fun p => x p.1 p.2)
  invFun y := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => y (i,j)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Flattening is an isometry, not merely a vector-space identification. -/
def flatten : BlockSpace (EuclideanSpace ℝ (Fin n)) ι ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (ι × Fin n) :=
  (flattenLinear (n := n) (ι := ι)).isometryOfInner (by
    intro x y
    simp [flattenLinear, PiLp.inner_apply, Fintype.sum_prod_type]
    rfl)

/-- The actual linear coordinate transformation on block operators. -/
def flattenEnd :
    (BlockSpace (EuclideanSpace ℝ (Fin n)) ι →ₗ[ℝ] BlockSpace (EuclideanSpace ℝ (Fin n)) ι) ≃ₗ[ℝ]
    (EuclideanSpace ℝ (ι × Fin n) →ₗ[ℝ] EuclideanSpace ℝ (ι × Fin n)) :=
  (flatten (n := n) (ι := ι)).toLinearEquiv.arrowCongr (flatten (n := n) (ι := ι)).toLinearEquiv

/-- Standard-coordinate matrix of a genuine block operator. -/
def blockMatrix :
    (BlockSpace (EuclideanSpace ℝ (Fin n)) ι →ₗ[ℝ] BlockSpace (EuclideanSpace ℝ (Fin n)) ι) ≃ₗ[ℝ]
      Matrix (ι × Fin n) (ι × Fin n) ℝ :=
  (flattenEnd (n := n) (ι := ι)).trans Matrix.toEuclideanLin.symm

/-- Literal insertion of a matrix into a chosen row/column block. -/
def embed (i j : ι) (M : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (ι × Fin n) (ι × Fin n) ℝ :=
  fun p q => if p.1 = i then if q.1 = j then M p.2 q.2 else 0 else 0

/-- A lifted operator is exactly the corresponding literal matrix block. -/
theorem flatten_liftBlock (i j : ι) (M : Matrix (Fin n) (Fin n) ℝ) :
    flattenEnd (LMICoefficients.liftBlock i j M.toEuclideanLin) =
      (embed i j M).toEuclideanLin := by
  ext x p
  rcases p with ⟨a,b⟩
  simp [flattenEnd, flatten, flattenLinear, LMICoefficients.liftBlock,
    ConeBlocks.inject, ConeBlocks.project, embed, Matrix.toLpLin_apply,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  change ((PiLp.single 2 i (WithLp.toLp 2 (M.mulVec (fun b => x (j,b))))) :
    BlockSpace (EuclideanSpace ℝ (Fin n)) ι) a b = _
  by_cases h : a = i <;> simp [h, PiLp.single_apply, Matrix.mulVec, dotProduct]

theorem blockMatrix_liftBlock (i j : ι)
    (T : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) :
    blockMatrix (LMICoefficients.liftBlock i j T) = embed i j (Matrix.toEuclideanLin.symm T) := by
  have h := flatten_liftBlock i j (Matrix.toEuclideanLin.symm T)
  rw [LinearEquiv.apply_symm_apply] at h
  simpa only [blockMatrix, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] using
    congrArg Matrix.toEuclideanLin.symm h

/-- Matrix action is exactly the flattened operator action. -/
theorem blockMatrix_action
    (T : BlockSpace (EuclideanSpace ℝ (Fin n)) ι →ₗ[ℝ] BlockSpace (EuclideanSpace ℝ (Fin n)) ι)
    (x : EuclideanSpace ℝ (ι × Fin n)) :
    (blockMatrix T).toEuclideanLin x = flatten (T (flatten.symm x)) := by
  change Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm (flattenEnd T)) x = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem blockMatrix_symmetric
    (T : BlockSpace (EuclideanSpace ℝ (Fin n)) ι →ₗ[ℝ] BlockSpace (EuclideanSpace ℝ (Fin n)) ι)
    (hT : T.IsSymmetric) : (blockMatrix T).IsHermitian := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  change (Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm (flattenEnd T))).IsSymmetric
  rw [LinearEquiv.apply_symm_apply]
  exact (LinearMap.isSymmetric_linearIsometryEquiv_conj_iff T flatten).mpr hT

/-- Strict operator positivity transfers to genuine matrix positive definiteness. -/
theorem blockMatrix_posDef
    (T : BlockSpace (EuclideanSpace ℝ (Fin n)) ι →ₗ[ℝ] BlockSpace (EuclideanSpace ℝ (Fin n)) ι)
    (hT : T.IsSymmetric) (hpos : ∀ x, x ≠ 0 → 0 < inner ℝ (T x) x) :
    (blockMatrix T).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (blockMatrix_symmetric T hT)
  intro x hx
  let z : EuclideanSpace ℝ (ι × Fin n) := WithLp.toLp 2 x
  have hz : z ≠ 0 := by
    intro h
    exact hx (congrArg WithLp.ofLp h)
  have hy : flatten.symm z ≠ 0 := by
    intro h
    apply hz
    have hh := congrArg (flatten (n := n) (ι := ι)) h
    simpa using hh
  have h : 0 < inner ℝ (flatten (T (flatten.symm z))) (flatten (flatten.symm z)) := by
    rw [LinearIsometryEquiv.inner_map_map]
    exact hpos _ hy
  rw [LinearIsometryEquiv.apply_symm_apply, ← blockMatrix_action] at h
  simpa [z, PiLp.inner_apply, Matrix.toLpLin_apply, dotProduct, mul_comm] using h

end Flatten

/-- Real adjoints correspond to transposes in the standard orthonormal bases. -/
theorem matrix_adjoint {a b : ℕ}
    (T : EuclideanSpace ℝ (Fin a) →ₗ[ℝ] EuclideanSpace ℝ (Fin b)) :
    Matrix.toEuclideanLin.symm T.adjoint = (Matrix.toEuclideanLin.symm T).transpose := by
  apply Matrix.toEuclideanLin.injective
  rw [LinearEquiv.apply_symm_apply]
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint (Matrix.toEuclideanLin.symm T)
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- The exact manuscript block LMI, with state block `none` followed by every `some i`. -/
def matrixLMI (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ) :
    Matrix (Option (Fin m) × Fin n) (Option (Fin m) × Fin n) ℝ :=
  embed none none (A*P + P*A.transpose + B*K + K.transpose*B.transpose + ρ • P) +
    ∑ i, (embed (some i) none (C i*P + D i*K) +
      embed none (some i) (C i*P + D i*K).transpose - embed (some i) (some i) P)

section Entries
variable (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ)

@[simp] theorem matrixLMI_state_state (a b : Fin n) :
    matrixLMI A B C D ρ P K (none,a) (none,b) =
      (A*P + P*A.transpose + B*K + K.transpose*B.transpose + ρ • P) a b := by
  simp [matrixLMI, embed, Matrix.sum_apply]

@[simp] theorem matrixLMI_noise_state (i : Fin m) (a b : Fin n) :
    matrixLMI A B C D ρ P K (some i,a) (none,b) = (C i*P + D i*K) a b := by
  simp [matrixLMI, embed, Matrix.sum_apply]

@[simp] theorem matrixLMI_state_noise (i : Fin m) (a b : Fin n) :
    matrixLMI A B C D ρ P K (none,a) (some i,b) = (C i*P + D i*K).transpose a b := by
  simp only [Matrix.transpose_add, Matrix.transpose_mul]
  simp [matrixLMI, embed, Matrix.sum_apply]

@[simp] theorem matrixLMI_noise_noise (i j : Fin m) (a b : Fin n) :
    matrixLMI A B C D ρ P K (some i,a) (some j,b) = if i = j then -P a b else 0 := by
  by_cases h : i = j <;> simp [matrixLMI, embed, Matrix.sum_apply, h, eq_comm]

/-- Every noise principal block of the negative LMI is the Lyapunov matrix itself. -/
theorem positive_lyapunov_of_matrix_lmi (i : Fin m)
    (h : (-matrixLMI A B C D ρ P K).PosDef) : P.PosDef := by
  have hp := h.submatrix (e := fun a : Fin n => (some i, a))
    (by intro a b h; exact congrArg Prod.snd h)
  have he : (-matrixLMI A B C D ρ P K).submatrix
      (fun a : Fin n => (some i, a)) (fun a : Fin n => (some i, a)) = P := by
    ext a b
    simp [Matrix.submatrix]
  rwa [he] at hp

end Entries

/-- The operator proved feasible by the cone alternative equals the stated matrix LMI. -/
theorem lmi_coordinate_identity (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (ρ : ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ) :
    blockMatrix (LMICoefficients.lmi A.toEuclideanLin B.toEuclideanLin
      (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)
      ρ P.toEuclideanLin K.toEuclideanLin) = matrixLMI A B C D ρ P K := by
  simp only [LMICoefficients.lmi, matrixLMI, map_add, map_sub, map_sum,
    blockMatrix_liftBlock, map_smul, Matrix.toLpLin_symm_comp, matrix_adjoint,
    LinearEquiv.symm_apply_apply, Matrix.transpose_add]



/-- Original real matrices and the original plain-coordinate flag imply strict feasibility
of the literal manuscript LMI. No LMI feasibility assumption is inserted. -/
theorem arbitrary_rate_matrix_feasible
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) (ρ : ℝ) :
    ∃ (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ),
      P.IsSymm ∧ (-(matrixLMI A B C D ρ P K)).PosDef := by
  have hf := (AdjointCoefficients.matrix_flag_bot_iff_euclidean A B C D n).mp hflag
  have hf' : (InputStructure.fromForward A.toEuclideanLin B.toEuclideanLin
      (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)).flag
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) = ⊥ := by
    simpa only [finrank_euclideanSpace_fin] using hf
  obtain ⟨P, K, hP, hneg⟩ := LMICoefficients.arbitrary_rate_feasible A.toEuclideanLin
    B.toEuclideanLin (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin) hf' ρ
  refine ⟨Matrix.toEuclideanLin.symm P, Matrix.toEuclideanLin.symm K, ?_, ?_⟩
  · apply Matrix.isHermitian_iff_isSymm.mp
    apply Matrix.isSymmetric_toEuclideanLin_iff.mp
    simpa only [LinearEquiv.apply_symm_apply] using hP
  · have hs := LMICoefficients.lmi_symmetric A.toEuclideanLin B.toEuclideanLin
      (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin) ρ P hP K
    have hs' : (-LMICoefficients.lmi A.toEuclideanLin B.toEuclideanLin
        (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin) ρ P K).IsSymmetric := by
      intro x y
      simpa only [LinearMap.neg_apply, inner_neg_left, inner_neg_right] using congrArg Neg.neg (hs x y)
    have hp := blockMatrix_posDef (-LMICoefficients.lmi A.toEuclideanLin B.toEuclideanLin
      (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin) ρ P K) hs'
      (fun x hx => PositiveCone.uniformPositive_strict _ hneg x hx)
    rw [map_neg] at hp
    have he := lmi_coordinate_identity A B C D ρ
      (Matrix.toEuclideanLin.symm P) (Matrix.toEuclideanLin.symm K)
    simp only [LinearEquiv.apply_symm_apply] at he
    rw [he] at hp
    exact hp

/-- In the paper's positive-noise-dimension regime, both strict matrix inequalities
are obtained directly from the original finite flag. -/
theorem arbitrary_rate_positive_matrix_feasible (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) (ρ : ℝ) :
    ∃ (P : Matrix (Fin n) (Fin n) ℝ) (K : Matrix (Fin r) (Fin n) ℝ),
      P.PosDef ∧ (-matrixLMI A B C D ρ P K).PosDef := by
  obtain ⟨P, K, _, h⟩ := arbitrary_rate_matrix_feasible A B C D hflag ρ
  exact ⟨P, K, positive_lyapunov_of_matrix_lmi A B C D ρ P K ⟨0,hm⟩ h, h⟩

#print axioms arbitrary_rate_positive_matrix_feasible
#print axioms lmi_coordinate_identity
#print axioms arbitrary_rate_matrix_feasible
end LinearStochastic.LMIMatrixCoordinates
