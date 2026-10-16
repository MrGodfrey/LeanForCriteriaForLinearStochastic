import LinearStochastic.AlgebraSurjectiveMatrices

/-!
# Coordinate invariance of the full obstruction iteration

Both state coordinates and observation coordinates may be changed by genuine
linear equivalences. The witness constraints are transported in both directions.
The final specialization identifies real matrix transposes with Euclidean adjoints.
-/
noncomputable section
namespace LinearStochastic.AdjointCoefficients
open Module
open scoped BigOperators

section General
variable {𝕜 E U F W ι : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup U] [Module 𝕜 U]
  [AddCommGroup F] [Module 𝕜 F] [AddCommGroup W] [Module 𝕜 W] [Fintype ι]
  (s : AdjointCoefficients (𝕜 := 𝕜) (E := E) (U := U) (ι := ι))
  (e : E ≃ₗ[𝕜] F) (f : U ≃ₗ[𝕜] W)

/-- Change of coordinates in the actual A†,B†,C†,D† coefficient maps. -/
def transport : AdjointCoefficients (𝕜 := 𝕜) (E := F) (U := W) (ι := ι) where
  A := e.toLinearMap.comp (s.A.comp e.symm.toLinearMap)
  B := f.toLinearMap.comp (s.B.comp e.symm.toLinearMap)
  C i := e.toLinearMap.comp ((s.C i).comp e.symm.toLinearMap)
  D i := f.toLinearMap.comp ((s.D i).comp e.symm.toLinearMap)

/-- Coordinate change commutes with a complete obstruction step, including all witnesses. -/
theorem obstruction_transport (S : Submodule 𝕜 E) :
    (s.transport e f).obstruction (S.map e.toLinearMap) =
      (s.obstruction S).map e.toLinearMap := by
  have hA (v : F) (w : ι → F) :
      (s.transport e f).A v + ∑ i, (s.transport e f).C i (w i) =
        e (s.A (e.symm v) + ∑ i, s.C i (e.symm (w i))) := by
    simp [transport]
  have hB (v : F) (w : ι → F) :
      (s.transport e f).B v + ∑ i, (s.transport e f).D i (w i) =
        f (s.B (e.symm v) + ∑ i, s.D i (e.symm (w i))) := by
    simp [transport]
  ext v
  rw [Submodule.mem_map_equiv]
  constructor
  · rintro ⟨hv, w, hw, hb, ha⟩
    refine ⟨(Submodule.mem_map_equiv S).mp hv, fun i => e.symm (w i),
      fun i => (Submodule.mem_map_equiv S).mp (hw i), ?_, ?_⟩
    · rw [hB] at hb
      apply f.injective
      simpa only [map_zero] using hb
    · rw [hA, Submodule.mem_map_equiv, e.symm_apply_apply] at ha
      exact ha
  · rintro ⟨hv, w, hw, hb, ha⟩
    refine ⟨(Submodule.mem_map_equiv S).mpr hv, fun i => e (w i),
      fun i => (Submodule.mem_map_equiv S).mpr (by simpa using hw i), ?_, ?_⟩
    · rw [hB]
      simp only [e.symm_apply_apply, hb, map_zero]
    · rw [hA, Submodule.mem_map_equiv, e.symm_apply_apply]
      simpa only [e.symm_apply_apply] using ha

/-- Every iterate, without dimension truncation, is invariant under these coordinates. -/
theorem flag_transport (k : ℕ) :
    (s.transport e f).flag k = (s.flag k).map e.toLinearMap := by
  induction k with
  | zero => simp [Submodule.map_top]
  | succ k ih => rw [flag_succ, ih, obstruction_transport, ← flag_succ]

/-- Coordinate transport preserves the vanishing obstruction test exactly. -/
theorem flag_transport_bot_iff (k : ℕ) :
    (s.transport e f).flag k = ⊥ ↔ s.flag k = ⊥ := by
  rw [flag_transport, Submodule.map_eq_bot_iff]

end General

section Matrices
variable {n r m : ℕ}
  (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
  (C : Fin m → Matrix (Fin n) (Fin n) ℝ)
  (D : Fin m → Matrix (Fin n) (Fin r) ℝ)

/-- Real Euclidean adjoints become exactly the transposed coefficient matrices. -/
theorem transport_fromForward_euclidean :
    (InputStructure.fromForward A.toEuclideanLin B.toEuclideanLin
      (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)).transport
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ))
      (WithLp.linearEquiv 2 ℝ (Fin r → ℝ)) = fromMatrices A B C D := by
  have ht {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) :
      M.toEuclideanLin.adjoint = M.transpose.toEuclideanLin := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
  simp only [transport, InputStructure.fromForward, fromMatrices, ht]
  rfl

/-- The plain real-coordinate flag used in the matrix-rank theorem is the same
as the Euclidean flag used with genuine adjoints and stochastic state models. -/
theorem matrix_flag_eq_euclidean_map (k : ℕ) :
    (fromMatrices A B C D).flag k =
      ((InputStructure.fromForward A.toEuclideanLin B.toEuclideanLin
        (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)).flag k).map
        (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap := by
  rw [← transport_fromForward_euclidean A B C D, flag_transport]

theorem matrix_flag_bot_iff_euclidean (k : ℕ) :
    (fromMatrices A B C D).flag k = ⊥ ↔
      (InputStructure.fromForward A.toEuclideanLin B.toEuclideanLin
        (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)).flag k = ⊥ := by
  rw [← transport_fromForward_euclidean A B C D, flag_transport_bot_iff]

/-- Numerical dimensions are also preserved by the proved state-coordinate change. -/
theorem matrix_flag_finrank_eq_euclidean (k : ℕ) :
    finrank ℝ ((fromMatrices A B C D).flag k) =
      finrank ℝ ((InputStructure.fromForward A.toEuclideanLin B.toEuclideanLin
        (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)).flag k) := by
  rw [matrix_flag_eq_euclidean_map, LinearEquiv.finrank_map_eq]

/-- The literal polynomial block matrices compute the Euclidean obstruction codimension too. -/
theorem finitePair_rank_codimension_euclidean (k : ℕ) :
    (Matrix.fromCols (Coordinates.finitePair A B C D k).2
      (Coordinates.finitePair A B C D k).1).rank -
      (Coordinates.finitePair A B C D k).2.rank =
      n - finrank ℝ ((InputStructure.fromForward A.toEuclideanLin B.toEuclideanLin
        (fun i => (C i).toEuclideanLin) (fun i => (D i).toEuclideanLin)).flag (k+1)) := by
  rw [Coordinates.finitePair_rank_codimension, matrix_flag_finrank_eq_euclidean]

/-- The canonical word-matrix test is equivalent to the very same ordinary-coordinate
flag used by the polynomial block-pair criterion, closing the last coordinate interface. -/
theorem matrix_flag_bot_iff_canonical_word_rank
    (hD : (SurjectiveMatrices.stack D).rank = m*n) :
    (fromMatrices A B C D).flag n = ⊥ ↔
      (WordMatrices.cumulativeMatrix (SurjectiveMatrices.reducedGenerators A B C D hD)
        (SurjectiveMatrices.reducedH B D hD) (n-1)).rank = n := by
  rw [matrix_flag_bot_iff_euclidean]
  exact SurjectiveMatrices.flag_bot_iff_word_matrix_full_rank A B C D hD

#print axioms matrix_flag_eq_euclidean_map
#print axioms matrix_flag_bot_iff_euclidean
#print axioms matrix_flag_bot_iff_canonical_word_rank
end Matrices
end LinearStochastic.AdjointCoefficients
