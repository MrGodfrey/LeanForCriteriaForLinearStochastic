module

public import LinearStochastic.AlgebraBlocks

@[expose] public section

/-!
# Exact reduced elimination inside an obstruction space

This file proves elimination from the actual obstruction constraints. The
coordinate map may have any finite index type. Floating point truncation and
numerical rank thresholds are not part of these exact statements.
-/
noncomputable section
namespace LinearStochastic.ReducedElimination
open Module
open scoped BigOperators

section Algebra
variable {𝕜 E U X Y ι : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup U] [Module 𝕜 U]
  [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y] [Fintype ι]
variable (s : AdjointCoefficients (𝕜 := 𝕜) (E := E) (U := U) (ι := ι))

/-- The two row blocks of manuscript `L_k`. -/
def reducedL (V : X →ₗ[𝕜] E) (Q : E →ₗ[𝕜] Y) : X →ₗ[𝕜] U × Y :=
  (s.B.comp V).prod (Q.comp (s.A.comp V))

/-- The two row blocks of manuscript `M_k`, retaining every noise channel. -/
def reducedM (V : X →ₗ[𝕜] E) (Q : E →ₗ[𝕜] Y) : (ι → X) →ₗ[𝕜] U × Y :=
  (∑ i, (s.D i).comp (V.comp (LinearMap.proj i))).prod
    (Q.comp (∑ i, (s.C i).comp (V.comp (LinearMap.proj i))))

/-- Reduced coordinates impose all state, channel and drift constraints;
no membership condition has been silently dropped. -/
theorem obstruction_eq_map_feasible (S : Submodule 𝕜 E)
    (V : X →ₗ[𝕜] E) (Q : E →ₗ[𝕜] Y)
    (hV : V.range = S) (hQ : Q.ker = S) :
    s.obstruction S = (feasibleSpace (reducedL s V Q) (reducedM s V Q)).map V := by
  ext v
  constructor
  · rintro ⟨hv, w, hw, hB, hA⟩
    obtain ⟨b, rfl⟩ := hV.symm ▸ hv
    have hwa : ∀ i, ∃ a, V a = w i := by
      intro i
      have hh : w i ∈ V.range := hV.symm ▸ hw i
      exact hh
    choose a ha using hwa
    refine ⟨b, ?_, rfl⟩
    apply (mem_feasibleSpace _ _ _).mpr
    refine ⟨a, ?_⟩
    simp only [reducedL, reducedM, LinearMap.prod_apply, Function.prod, LinearMap.comp_apply,
      LinearMap.sum_apply, LinearMap.proj_apply]
    apply Prod.ext
    · change s.B (V b) + ∑ i, s.D i (V (a i)) = 0
      simpa only [ha] using hB
    · change Q (s.A (V b)) + Q (∑ i, s.C i (V (a i))) = 0
      rw [← map_add]
      change s.A (V b) + ∑ i, s.C i (V (a i)) ∈ Q.ker
      rw [hQ]
      simpa only [ha] using hA
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨a, ha⟩ := (mem_feasibleSpace _ _ _).mp hb
    simp only [reducedL, reducedM, LinearMap.prod_apply, Function.prod, LinearMap.comp_apply,
      LinearMap.sum_apply, LinearMap.proj_apply] at ha
    refine ⟨hV ▸ ⟨b, rfl⟩, fun i => V (a i), fun i => hV ▸ ⟨a i, rfl⟩, ?_, ?_⟩
    · exact congrArg Prod.fst ha
    · have h := congrArg Prod.snd ha
      change Q (s.A (V b)) + Q (∑ i, s.C i (V (a i))) = 0 at h
      rw [← map_add] at h
      exact hQ ▸ h

end Algebra

section Orthogonal
variable {X F G H : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Left-kernel elimination is exact. Orthonormality is more than needed:
spanning `ker M†` already determines the same residual kernel. -/
theorem feasible_eq_residual_ker (L : X →ₗ[ℝ] G) (M : F →ₗ[ℝ] G)
    (U₀ : H →ₗ[ℝ] G) (hU : U₀.range = M.adjoint.ker) :
    feasibleSpace L M = (U₀.adjoint.comp L).ker := by
  have hk : U₀.adjoint.ker = M.range := by
    rw [← U₀.orthogonal_range, hU, M.adjoint.orthogonal_ker,
      LinearMap.adjoint_adjoint]
  rw [LinearMap.ker_comp, hk]
  rfl

/-- The residual rank is precisely the dimension removed at this step. -/
theorem residual_rank_eq_dimension_drop (L : X →ₗ[ℝ] G) (M : F →ₗ[ℝ] G)
    (U₀ : H →ₗ[ℝ] G) (hU : U₀.range = M.adjoint.ker) :
    finrank ℝ (U₀.adjoint.comp L).range =
      finrank ℝ X - finrank ℝ (feasibleSpace L M) := by
  rw [feasible_eq_residual_ker L M U₀ hU]
  have := (U₀.adjoint.comp L).finrank_range_add_finrank_ker
  omega

/-- Removed directions form the orthogonal complement of the next space
inside the current space, exactly as in the manuscript's basis update. -/
theorem current_space_orthogonal_split (S N : Submodule ℝ X) (h : N ≤ S) :
    N ⊔ (Nᗮ ⊓ S) = S ∧ Disjoint N (Nᗮ ⊓ S) := by
  exact ⟨Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection h,
    N.orthogonal_disjoint.mono_right inf_le_left⟩

/-- Appending the removed directions to the old orthogonal complement gives
the new orthogonal complement, without losing or duplicating a direction. -/
theorem complement_update (S N : Submodule ℝ X) (h : N ≤ S) :
    Sᗮ ⊔ (Nᗮ ⊓ S) = Nᗮ ∧ Disjoint Sᗮ (Nᗮ ⊓ S) := by
  have he := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
    (Submodule.orthogonal_le h)
  rw [Submodule.orthogonal_orthogonal] at he
  refine ⟨?_, ?_⟩
  · simpa only [inf_comm] using he
  · exact S.orthogonal_disjoint.symm.mono_right inf_le_right

end Orthogonal
end LinearStochastic.ReducedElimination
