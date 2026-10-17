module

public import LinearStochastic.ReducedElimination
public import Mathlib.Analysis.InnerProductSpace.ProdL2

@[expose] public section

/-!
# A fully constructed exact orthogonal-elimination algorithm

The row residual is formed from the original adjoint coefficients, using an
orthonormal basis of the actual left kernel. The O₀/O₁ coordinate frames and
Q/V updates are constructed, not assumed. `iterate` uses its updated basis at
every later step. The final theorems prove agreement with the obstruction flag,
its prescribed block-pair rank difference, and termination by dim E.
This is exact arithmetic; numerical rank tolerances and the stochastic
controllability classification are separate statements.
-/
noncomputable section
namespace LinearStochastic.Staircase
open Module
open scoped BigOperators InnerProductSpace

section Frames
variable {E X Y Z : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- Actual orthonormal columns of a subspace; existence is supplied by finite-dimensional Gram-Schmidt. -/
def frame (S : Submodule ℝ E) : EuclideanSpace ℝ (Fin (finrank ℝ S)) →ₗᵢ[ℝ] E :=
  S.subtypeₗᵢ.comp (stdOrthonormalBasis ℝ S).repr.symm.toLinearIsometry

theorem frame_range (S : Submodule ℝ E) : (frame S).range = S := by
  change (S.subtype.comp (stdOrthonormalBasis ℝ S).repr.symm.toLinearEquiv.toLinearMap).range = S
  rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]

/-- Horizontal concatenation of two orthogonal column isometries. -/
def append (Q : Y →ₗᵢ[ℝ] E) (W : Z →ₗᵢ[ℝ] E)
    (h : W.range ≤ Q.rangeᗮ) : WithLp 2 (Y × Z) →ₗᵢ[ℝ] E :=
  ((Q.toLinearMap.coprod W.toLinearMap).comp
    (WithLp.linearEquiv 2 ℝ (Y × Z)).toLinearMap).isometryOfInner (by
      intro x y
      change ⟪Q x.fst + W x.snd, Q y.fst + W y.snd⟫_ℝ = _
      rw [inner_add_left, inner_add_right, inner_add_right]
      have h₁ : ⟪Q x.fst, W y.snd⟫_ℝ = 0 :=
        Submodule.inner_right_of_mem_orthogonal (K := Q.range) ⟨_, rfl⟩ (h ⟨_, rfl⟩)
      have h₂ : ⟪W x.snd, Q y.fst⟫_ℝ = 0 :=
        Submodule.inner_left_of_mem_orthogonal (K := Q.range) ⟨_, rfl⟩ (h ⟨_, rfl⟩)
      simp only [h₁, h₂, add_zero, zero_add, Q.inner_map_map, W.inner_map_map]
      rfl)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z] in
theorem append_apply (Q : Y →ₗᵢ[ℝ] E) (W : Z →ₗᵢ[ℝ] E)
    (h : W.range ≤ Q.rangeᗮ) (x : WithLp 2 (Y × Z)) :
    append Q W h x = Q x.fst + W x.snd := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z] in
theorem append_range (Q : Y →ₗᵢ[ℝ] E) (W : Z →ₗᵢ[ℝ] E)
    (h : W.range ≤ Q.rangeᗮ) : (append Q W h).range = Q.range ⊔ W.range := by
  change ((Q.toLinearMap.coprod W.toLinearMap).comp
    (WithLp.linearEquiv 2 ℝ (Y × Z)).toLinearMap).range = _
  rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, LinearMap.range_coprod]

/-- O₀ is the actual orthonormal basis of ker R retained by the update. -/
def retained (V : X →ₗᵢ[ℝ] E) (R : X →ₗ[ℝ] Z) :
    EuclideanSpace ℝ (Fin (finrank ℝ R.ker)) →ₗᵢ[ℝ] E := V.comp (frame R.ker)

/-- O₁ is the actual orthonormal basis of (ker R)⊥ removed by the update. -/
def removed (V : X →ₗᵢ[ℝ] E) (R : X →ₗ[ℝ] Z) :
    EuclideanSpace ℝ (Fin (finrank ℝ R.kerᗮ)) →ₗᵢ[ℝ] E := V.comp (frame R.kerᗮ)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z] in
theorem retained_range (V : X →ₗᵢ[ℝ] E) (R : X →ₗ[ℝ] Z) :
    (retained V R).range = R.ker.map V.toLinearMap := by
  change (V.toLinearMap.comp (frame R.ker).toLinearMap).range = _
  rw [LinearMap.range_comp, frame_range]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ Z] in
theorem removed_range (V : X →ₗᵢ[ℝ] E) (R : X →ₗ[ℝ] Z) :
    (removed V R).range = (retained V R).rangeᗮ ⊓ V.range := by
  change (V.toLinearMap.comp (frame R.kerᗮ).toLinearMap).range = _
  rw [LinearMap.range_comp, frame_range, Submodule.map_orthogonal, retained_range]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z] in
theorem removed_orthogonal_old (Q : Y →ₗᵢ[ℝ] E) (V : X →ₗᵢ[ℝ] E)
    (hQV : Q.range = V.rangeᗮ) (R : X →ₗ[ℝ] Z) :
    (removed V R).range ≤ Q.rangeᗮ := by
  rw [hQV, Submodule.orthogonal_orthogonal, removed_range]
  exact inf_le_right

/-- The paper's literal update [Q,V O₁], with the new columns appended in order. -/
def nextComplement (Q : Y →ₗᵢ[ℝ] E) (V : X →ₗᵢ[ℝ] E)
    (hQV : Q.range = V.rangeᗮ) (R : X →ₗ[ℝ] Z) :
    WithLp 2 (Y × EuclideanSpace ℝ (Fin (finrank ℝ R.kerᗮ))) →ₗᵢ[ℝ] E :=
  append Q (removed V R) (removed_orthogonal_old Q V hQV R)

omit [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z] in
/-- The constructed updates remain mutually orthogonal and complete. -/
theorem nextComplement_range (Q : Y →ₗᵢ[ℝ] E) (V : X →ₗᵢ[ℝ] E)
    (hQV : Q.range = V.rangeᗮ) (R : X →ₗ[ℝ] Z) :
    (nextComplement Q V hQV R).range = (retained V R).rangeᗮ := by
  have hn : (retained V R).range ≤ V.range := by
    rw [retained_range]
    rintro x ⟨v, _, rfl⟩
    exact ⟨v, rfl⟩
  rw [nextComplement, append_range, hQV, removed_range]
  exact (ReducedElimination.complement_update V.range (retained V R).range hn).1

omit [FiniteDimensional ℝ Z] in
/-- The number of appended O₁ columns is exactly rank R. -/
theorem removed_dimension (R : X →ₗ[ℝ] Z) :
    finrank ℝ R.kerᗮ = finrank ℝ R.range := by
  have h₁ := R.ker.finrank_add_finrank_orthogonal
  have h₂ := R.finrank_range_add_finrank_ker
  omega

omit [FiniteDimensional ℝ Z] in
/-- The dimension of the next complementary coordinate space increases by rank R. -/
theorem nextComplement_dimension (R : X →ₗ[ℝ] Z) :
    finrank ℝ (WithLp 2 (Y × EuclideanSpace ℝ (Fin (finrank ℝ R.kerᗮ)))) =
      finrank ℝ Y + finrank ℝ R.range := by
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod,
    finrank_euclideanSpace_fin, removed_dimension]

/-- The chosen O=[O₁,O₀] is itself a complete orthogonal coordinate map. -/
def splitFrame (R : X →ₗ[ℝ] Z) :
    WithLp 2 (EuclideanSpace ℝ (Fin (finrank ℝ R.kerᗮ)) ×
      EuclideanSpace ℝ (Fin (finrank ℝ R.ker))) →ₗᵢ[ℝ] X :=
  append (frame R.kerᗮ) (frame R.ker) (by
    rw [frame_range, frame_range, Submodule.orthogonal_orthogonal])

omit [FiniteDimensional ℝ Z] in
theorem splitFrame_range (R : X →ₗ[ℝ] Z) : (splitFrame R).range = ⊤ := by
  rw [splitFrame, append_range, frame_range, frame_range]
  rw [sup_comm]
  exact R.ker.isCompl_orthogonal.sup_eq_top

end Frames


section ActualResidual
variable {E U X Y ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y] [Fintype ι]
variable (s : AdjointCoefficients (𝕜 := ℝ) (E := E) (U := U) (ι := ι))
  (Q : Y →ₗᵢ[ℝ] E) (V : X →ₗᵢ[ℝ] E)

/-- The two actual reduced L blocks in the Hilbert direct sum of their row spaces. -/
def rowL : X →ₗ[ℝ] WithLp 2 (U × Y) :=
  (WithLp.linearEquiv 2 ℝ (U × Y)).symm.toLinearMap.comp
    (ReducedElimination.reducedL s V.toLinearMap Q.toLinearMap.adjoint)

/-- The actual reduced M blocks, with all channel coordinates represented isometrically. -/
def rowM : PiLp 2 (fun _ : ι => X) →ₗ[ℝ] WithLp 2 (U × Y) :=
  (WithLp.linearEquiv 2 ℝ (U × Y)).symm.toLinearMap.comp
    ((ReducedElimination.reducedM s V.toLinearMap Q.toLinearMap.adjoint).comp
      (WithLp.linearEquiv 2 ℝ (ι → X)).toLinearMap)

/-- Construct U₀ from a real orthonormal basis of ker M†, then form R=U₀†L. -/
def residual : X →ₗ[ℝ]
    EuclideanSpace ℝ (Fin (finrank ℝ (rowM s Q V).adjoint.ker)) :=
  (frame (rowM s Q V).adjoint.ker).toLinearMap.adjoint.comp (rowL s Q V)

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ X] in
theorem feasible_rows :
    feasibleSpace (rowL s Q V) (rowM s Q V) =
      feasibleSpace (ReducedElimination.reducedL s V.toLinearMap Q.toLinearMap.adjoint)
        (ReducedElimination.reducedM s V.toLinearMap Q.toLinearMap.adjoint) := by
  ext x
  rw [mem_feasibleSpace, mem_feasibleSpace]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.ofLp, ?_⟩
    have ht := congrArg (WithLp.linearEquiv 2 ℝ (U × Y)) hw
    simpa [rowL, rowM] using ht
  · rintro ⟨w, hw⟩
    refine ⟨WithLp.toLp 2 w, ?_⟩
    have ht := congrArg (WithLp.linearEquiv 2 ℝ (U × Y)).symm hw
    simpa [rowL, rowM] using ht

/-- The residual is formed from the original constraints, and its kernel is exactly the next flag. -/
theorem residual_exact (hQV : Q.range = V.rangeᗮ) :
    s.obstruction V.range = (residual s Q V).ker.map V.toLinearMap := by
  have hQ : Q.toLinearMap.adjoint.ker = V.range := by
    rw [← Q.toLinearMap.orthogonal_range]
    change Q.rangeᗮ = V.range
    rw [hQV, Submodule.orthogonal_orthogonal]
  rw [ReducedElimination.obstruction_eq_map_feasible s V.range V.toLinearMap
    Q.toLinearMap.adjoint rfl hQ, ← feasible_rows s Q V]
  rw [ReducedElimination.feasible_eq_residual_ker (rowL s Q V) (rowM s Q V)
    (frame (rowM s Q V).adjoint.ker).toLinearMap (frame_range _)]
  rfl

/-- The concrete V O₀ update realizes the next obstruction space. -/
theorem retained_exact (hQV : Q.range = V.rangeᗮ) :
    (retained V (residual s Q V)).range = s.obstruction V.range := by
  rw [retained_range, residual_exact s Q V hQV]

/-- The concrete appended Q update realizes the whole new orthogonal complement. -/
theorem complement_exact (hQV : Q.range = V.rangeᗮ) :
    (nextComplement Q V hQV (residual s Q V)).range = (s.obstruction V.range)ᗮ := by
  rw [nextComplement_range, retained_exact s Q V hQV]

/-- Each residual rank is exactly the number of state dimensions lost. -/
theorem residual_dimension_drop (hQV : Q.range = V.rangeᗮ) :
    finrank ℝ (residual s Q V).range =
      finrank ℝ V.range - finrank ℝ (s.obstruction V.range) := by
  have hV := LinearMap.finrank_range_of_inj V.injective
  have hK := LinearMap.finrank_range_of_inj
    (f := V.toLinearMap.comp (residual s Q V).ker.subtype)
    (by intro a b hab; apply Subtype.ext; exact V.injective hab)
  change finrank ℝ (V.toLinearMap.comp (residual s Q V).ker.subtype).range =
    finrank ℝ (residual s Q V).ker at hK
  rw [LinearMap.range_comp, Submodule.range_subtype, ← residual_exact s Q V hQV] at hK
  have hR := (residual s Q V).finrank_range_add_finrank_ker
  change finrank ℝ V.range = finrank ℝ X at hV
  omega

/-- Complement dimensions accumulate exactly the true residual ranks. -/
theorem codimension_increment (hQV : Q.range = V.rangeᗮ) :
    finrank ℝ E - finrank ℝ (s.obstruction V.range) =
      (finrank ℝ E - finrank ℝ V.range) + finrank ℝ (residual s Q V).range := by
  rw [residual_dimension_drop s Q V hQV]
  have hS := Submodule.finrank_le V.range
  have hN := Submodule.finrank_mono (s.obstruction_le V.range)
  omega

end ActualResidual


section Cumulative
variable {E U ι : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [Fintype ι]
variable (s : AdjointCoefficients (𝕜 := ℝ) (E := E) (U := U) (ι := ι))

/-- A concrete residual rank at stage k, with constructed orthonormal coordinate frames. -/
def stepRank (k : ℕ) : ℕ :=
  finrank ℝ (residual s (frame (s.flag k)ᗮ) (frame (s.flag k))).range

omit [FiniteDimensional ℝ U] in
/-- The canonical frames satisfy the same invariant as every updated complete orthogonal basis. -/
theorem flag_frames_complement (k : ℕ) :
    (frame (s.flag k)ᗮ).range = (frame (s.flag k)).rangeᗮ := by
  rw [frame_range, frame_range]

theorem stepRank_dimension_drop (k : ℕ) :
    stepRank s k = finrank ℝ (s.flag k) - finrank ℝ (s.flag (k+1)) := by
  unfold stepRank
  rw [residual_dimension_drop s _ _ (flag_frames_complement s k), frame_range]
  rfl

theorem codimension_step (k : ℕ) :
    finrank ℝ E - finrank ℝ (s.flag (k+1)) =
      (finrank ℝ E - finrank ℝ (s.flag k)) + stepRank s k := by
  rw [stepRank_dimension_drop]
  have hS := Submodule.finrank_le (s.flag k)
  have hN := Submodule.finrank_mono (s.flag_step_le k)
  omega

/-- Every computed rank increment sums to the exact current codimension. -/
theorem sum_stepRank (k : ℕ) :
    ∑ j ∈ Finset.range k, stepRank s j = finrank ℝ E - finrank ℝ (s.flag k) := by
  induction k with
  | zero =>
    change 0 = finrank ℝ E - finrank ℝ (⊤ : Submodule ℝ E)
    rw [finrank_top, Nat.sub_self]
  | succ k ih => rw [Finset.sum_range_succ, ih, ← codimension_step]

/-- The prescribed block-pair rank difference, including the paper's δ₀=0. -/
def prescribedDelta : ℕ → ℕ
  | 0 => 0
  | k+1 => finrank ℝ ((s.blockPair k).N.coprod (s.blockPair k).K).range -
      finrank ℝ (s.blockPair k).N.range

theorem prescribedDelta_eq_codimension (k : ℕ) :
    prescribedDelta s k = finrank ℝ E - finrank ℝ (s.flag k) := by
  cases k with
  | zero =>
    change 0 = finrank ℝ E - finrank ℝ (⊤ : Submodule ℝ E)
    rw [finrank_top, Nat.sub_self]
  | succ k => exact s.blockPair_rank_codimension k

/-- qₖ=δₖ for the accumulated orthogonal complement. -/
theorem complement_dimension_eq_prescribedDelta (k : ℕ) :
    finrank ℝ (s.flag k)ᗮ = prescribedDelta s k := by
  rw [prescribedDelta_eq_codimension]
  have h := (s.flag k).finrank_add_finrank_orthogonal
  omega

/-- Δqₖ=δₖ₊₁−δₖ, with the actual residual rank on the left. -/
theorem stepRank_eq_prescribedDelta_increment (k : ℕ) :
    stepRank s k = prescribedDelta s (k+1) - prescribedDelta s k := by
  rw [prescribedDelta_eq_codimension, prescribedDelta_eq_codimension, codimension_step]
  omega

/-- The accumulated ranks are exactly the block-pair rank difference. -/
theorem sum_stepRank_eq_prescribedDelta (k : ℕ) :
    ∑ j ∈ Finset.range k, stepRank s j = prescribedDelta s k := by
  rw [sum_stepRank, prescribedDelta_eq_codimension]

/-- A zero residual rank means the iteration has reached a fixed space. -/
theorem stepRank_zero_iff_stationary (k : ℕ) :
    stepRank s k = 0 ↔ s.flag (k+1) = s.flag k := by
  rw [stepRank_dimension_drop]
  constructor
  · intro h
    apply Submodule.eq_of_le_of_finrank_eq (s.flag_step_le k)
    have hm := Submodule.finrank_mono (s.flag_step_le k)
    omega
  · intro h
    rw [h, Nat.sub_self]

/-- The constructed elimination reaches a stationary space within the n-step bound. -/
theorem stepRank_zero_at_dimension : stepRank s (finrank ℝ E) = 0 := by
  rw [stepRank_zero_iff_stationary, AdjointCoefficients.flag_succ]
  exact s.flag_stable_at_finrank

/-- No dimension is lost after termination. -/
theorem stationary_after_zero (k : ℕ) (h : stepRank s k = 0) (j : ℕ) :
    s.flag (k+j) = s.flag k := by
  exact s.stationary_of_step_eq ((stepRank_zero_iff_stationary s k).mp h) j

#print axioms residual_exact
#print axioms nextComplement_range
#print axioms sum_stepRank_eq_prescribedDelta
#print axioms stepRank_zero_at_dimension
variable {X Y : Type}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- A single exact update preserves the induction invariant and gives the prescribed
rank increments for any orthogonal coordinates, not just the canonical frame choice. -/
theorem staircase_step (Q : Y →ₗᵢ[ℝ] E) (V : X →ₗᵢ[ℝ] E)
    (hQV : Q.range = V.rangeᗮ) (k : ℕ) (hV : V.range = s.flag k) :
    (retained V (residual s Q V)).range = s.flag (k+1) ∧
    (nextComplement Q V hQV (residual s Q V)).range = (s.flag (k+1))ᗮ ∧
    finrank ℝ Y = prescribedDelta s k ∧
    finrank ℝ (residual s Q V).range = prescribedDelta s (k+1) - prescribedDelta s k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [retained_exact s Q V hQV, hV]
    rfl
  · rw [complement_exact s Q V hQV, hV]
    rfl
  · have hQ := LinearMap.finrank_range_of_inj Q.injective
    change finrank ℝ Q.range = finrank ℝ Y at hQ
    rw [hQV, hV, complement_dimension_eq_prescribedDelta s k] at hQ
    exact hQ.symm
  · rw [residual_dimension_drop s Q V hQV, hV]
    rw [← stepRank_eq_prescribedDelta_increment s k, stepRank_dimension_drop]
    rfl

end Cumulative


section Algorithm
variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A full orthogonal state basis, with its current coordinate spaces.
This data records orthogonality only; agreement with the obstruction iteration is a theorem. -/
structure FrameState where
  QSpace : Type
  [qNorm : NormedAddCommGroup QSpace]
  [qInner : InnerProductSpace ℝ QSpace]
  [qFinite : FiniteDimensional ℝ QSpace]
  VSpace : Type
  [vNorm : NormedAddCommGroup VSpace]
  [vInner : InnerProductSpace ℝ VSpace]
  [vFinite : FiniteDimensional ℝ VSpace]
  Q : QSpace →ₗᵢ[ℝ] E
  V : VSpace →ₗᵢ[ℝ] E
  complementary : Q.range = V.rangeᗮ

attribute [instance] FrameState.qNorm FrameState.qInner FrameState.qFinite
  FrameState.vNorm FrameState.vInner FrameState.vFinite

/-- The complete matrix [Q,V] as an actual linear isometry. -/
def FrameState.assembled (t : FrameState E) : WithLp 2 (t.QSpace × t.VSpace) →ₗᵢ[ℝ] E :=
  append t.Q t.V (by rw [t.complementary, Submodule.orthogonal_orthogonal])

omit [FiniteDimensional ℝ E] in
/-- Completeness of the assembled orthogonal state basis is proved from its ranges. -/
theorem FrameState.assembled_range (t : FrameState E) : (FrameState.assembled E t).range = ⊤ := by
  rw [FrameState.assembled, append_range, t.complementary, sup_comm]
  exact t.V.range.isCompl_orthogonal.sup_eq_top

/-- Q₀ has no directions and V₀ is the identity, exactly as initialized in the paper. -/
def initial : FrameState E where
  QSpace := (⊥ : Submodule ℝ E)
  VSpace := E
  Q := (⊥ : Submodule ℝ E).subtypeₗᵢ
  V := LinearIsometry.id
  complementary := by
    change (⊥ : Submodule ℝ E).subtype.range = (LinearMap.id : E →ₗ[ℝ] E).rangeᗮ
    rw [Submodule.range_subtype, LinearMap.range_id, Submodule.top_orthogonal_eq_bot]

variable {E} {U ι : Type}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [Fintype ι]
  (s : AdjointCoefficients (𝕜 := ℝ) (E := E) (U := U) (ι := ι))

/-- One fully constructed orthogonal-elimination step. -/
def update (t : FrameState E) : FrameState E where
  QSpace := WithLp 2 (t.QSpace ×
    EuclideanSpace ℝ (Fin (finrank ℝ (residual s t.Q t.V).kerᗮ)))
  VSpace := EuclideanSpace ℝ (Fin (finrank ℝ (residual s t.Q t.V).ker))
  Q := nextComplement t.Q t.V t.complementary (residual s t.Q t.V)
  V := retained t.V (residual s t.Q t.V)
  complementary := nextComplement_range t.Q t.V t.complementary (residual s t.Q t.V)

/-- The actual algorithm, using the updated basis at every following stage. -/
def iterate : ℕ → FrameState E
  | 0 => initial E
  | k+1 => update s (iterate k)

/-- The computed V coordinate columns agree with every obstruction iterate. -/
theorem iterate_range (k : ℕ) : (iterate s k).V.range = s.flag k := by
  induction k with
  | zero =>
    change (LinearMap.id : E →ₗ[ℝ] E).range = s.flag 0
    rw [LinearMap.range_id, AdjointCoefficients.flag_zero]
  | succ k ih =>
    change (retained (iterate s k).V
      (residual s (iterate s k).Q (iterate s k).V)).range = _
    rw [retained_exact s _ _ (iterate s k).complementary, ih]
    rfl

/-- The computed Q columns span exactly the current orthogonal complement. -/
theorem iterate_complement_range (k : ℕ) : (iterate s k).Q.range = (s.flag k)ᗮ := by
  rw [(iterate s k).complementary, iterate_range]

/-- The actual number of Q coordinate columns is δₖ, for the recursively updated basis. -/
theorem iterate_dimension (k : ℕ) : finrank ℝ (iterate s k).QSpace = prescribedDelta s k := by
  have h := LinearMap.finrank_range_of_inj (iterate s k).Q.injective
  change finrank ℝ (iterate s k).Q.range = finrank ℝ (iterate s k).QSpace at h
  rw [iterate_complement_range, complement_dimension_eq_prescribedDelta] at h
  exact h.symm

/-- Actual residual ranks are the proved, coordinate-independent rank increments. -/
theorem iterate_residual_rank (k : ℕ) :
    finrank ℝ (residual s (iterate s k).Q (iterate s k).V).range =
      prescribedDelta s (k+1) - prescribedDelta s k :=
  (staircase_step s (iterate s k).Q (iterate s k).V
    (iterate s k).complementary k (iterate_range s k)).2.2.2

/-- The computed state has stabilized by n updates. -/
theorem iterate_stationary_at_dimension :
    (iterate s (finrank ℝ E + 1)).V.range = (iterate s (finrank ℝ E)).V.range := by
  rw [iterate_range, iterate_range, AdjointCoefficients.flag_succ]
  exact s.flag_stable_at_finrank

/-- The accumulated Q dimensions start at zero, without an assumed initialization invariant. -/
theorem initial_dimension : finrank ℝ (iterate s 0).QSpace = 0 := by
  rw [iterate_dimension]
  rfl

#print axioms iterate_range
#print axioms iterate_dimension
#print axioms iterate_residual_rank
#print axioms iterate_stationary_at_dimension
/-- At the bound the residual itself has rank zero, so the stopping test succeeds. -/
theorem iterate_residual_zero_at_dimension :
    finrank ℝ (residual s (iterate s (finrank ℝ E)).Q (iterate s (finrank ℝ E)).V).range = 0 := by
  rw [iterate_residual_rank, ← stepRank_eq_prescribedDelta_increment]
  exact stepRank_zero_at_dimension s

/-- The retained and removed coordinate dimensions exhaust the ambient state dimension. -/
theorem iterate_coordinate_dimensions (k : ℕ) :
    finrank ℝ (iterate s k).QSpace + finrank ℝ (iterate s k).VSpace = finrank ℝ E := by
  have hV := LinearMap.finrank_range_of_inj (iterate s k).V.injective
  change finrank ℝ (iterate s k).V.range = finrank ℝ (iterate s k).VSpace at hV
  rw [iterate_range] at hV
  rw [iterate_dimension, ← complement_dimension_eq_prescribedDelta, ← hV, add_comm]
  exact (s.flag k).finrank_add_finrank_orthogonal

/-- The current state-coordinate width is exactly dₖ=n−δₖ. -/
theorem iterate_state_dimension (k : ℕ) :
    finrank ℝ (iterate s k).VSpace = finrank ℝ E - prescribedDelta s k := by
  have h := iterate_coordinate_dimensions s k
  rw [iterate_dimension] at h
  omega

/-- The two reduced row blocks have precisely r+qₖ rows. -/
theorem iterate_row_dimension (k : ℕ) :
    finrank ℝ (WithLp 2 (U × (iterate s k).QSpace)) = finrank ℝ U + prescribedDelta s k := by
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod, iterate_dimension]

/-- The channel unknowns have precisely m dₖ coordinates. -/
theorem iterate_channel_dimension (k : ℕ) :
    finrank ℝ (PiLp 2 (fun _ : ι => (iterate s k).VSpace)) =
      Fintype.card ι * (finrank ℝ E - prescribedDelta s k) := by
  rw [(WithLp.linearEquiv 2 ℝ (ι → (iterate s k).VSpace)).finrank_eq]
  simp [Module.finrank_pi_fintype, iterate_state_dimension]

#print axioms iterate_residual_zero_at_dimension
end Algorithm
end LinearStochastic.Staircase
