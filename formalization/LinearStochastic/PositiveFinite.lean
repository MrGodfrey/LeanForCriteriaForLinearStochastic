module

public import LinearStochastic.PositiveCone
public import LinearStochastic.LMIMatrixCoordinates

@[expose] public section

set_option maxHeartbeats 800000
noncomputable section
namespace LinearStochastic.PositiveFinite
open scoped InnerProductSpace
open PositiveCone ConeBlocks LMIMatrixCoordinates
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Compactness of the actual unit sphere turns strict quadratic positivity
into a uniform margin. The zero-dimensional space is included explicitly. -/
theorem uniformPositive_of_strict (T : E →L[ℝ] E)
    (hT : ∀ x, x ≠ 0 → 0 < inner ℝ (T x) x) : UniformPositive T := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · letI := hE
    refine ⟨1, zero_lt_one, ?_⟩
    intro x
    have hx : x = 0 := Subsingleton.elim _ _
    simp [hx]
  · letI := hE
    have hc : Continuous (fun x : E => inner ℝ (T x) x) := T.continuous.inner continuous_id
    have hs : (Metric.sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
    obtain ⟨z, hz, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hs hc.continuousOn
    have hzNorm : ‖z‖ = 1 := by simpa using hz
    have hzne : z ≠ 0 := by intro h; simp [h] at hzNorm
    refine ⟨inner ℝ (T z) z, hT z hzne, ?_⟩
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have hunit : (‖x‖⁻¹ : ℝ) • x ∈ Metric.sphere (0 : E) 1 := by
        simpa using norm_smul_inv_norm (𝕜 := ℝ) hx
      have hm := hmin hunit
      change inner ℝ (T z) z ≤ inner ℝ (T ((‖x‖⁻¹ : ℝ) • x)) ((‖x‖⁻¹ : ℝ) • x) at hm
      have hscale : inner ℝ (T ((‖x‖⁻¹ : ℝ) • x)) ((‖x‖⁻¹ : ℝ) • x) =
          inner ℝ (T x) x / ‖x‖^2 := by
        simp only [map_smul, inner_smul_left, inner_smul_right, conj_trivial, div_eq_mul_inv]
        ring
      rw [hscale] at hm
      exact (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hx))).mp hm

theorem uniformPositive_iff_strict (T : E →L[ℝ] E) :
    UniformPositive T ↔ ∀ x, x ≠ 0 → 0 < inner ℝ (T x) x :=
  ⟨uniformPositive_strict T, uniformPositive_of_strict T⟩

theorem matrix_uniformPositive {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : M.PosDef) :
    UniformPositive M.toEuclideanLin.toContinuousLinearMap := by
  apply uniformPositive_of_strict
  intro x hx
  have hx' : WithLp.ofLp x ≠ 0 := by
    intro h
    exact hx (congrArg (WithLp.toLp 2) h)
  have h := hM.dotProduct_mulVec_pos hx'
  simpa [PiLp.inner_apply, Matrix.toLpLin_apply, dotProduct, mul_comm] using h

local instance blockNormedSpace {n : ℕ} {ι : Type*} [Fintype ι] :
    NormedSpace ℝ (BlockSpace (EuclideanSpace ℝ (Fin n)) ι) :=
  PiLp.normedSpace 2 ℝ (fun _ : ι => EuclideanSpace ℝ (Fin n))

/-- The coordinate correspondence works in both directions for strict positivity. -/
theorem blockMatrix_uniformPositive
    {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : BlockSpace (EuclideanSpace ℝ (Fin n)) ι →L[ℝ]
      BlockSpace (EuclideanSpace ℝ (Fin n)) ι)
    (h : (blockMatrix T.toLinearMap).PosDef) : UniformPositive T := by
  apply uniformPositive_of_strict
  intro x hx
  have hx' : flatten (n := n) (ι := ι) x ≠ 0 := by
    intro h
    exact hx (flatten.injective (by simpa using h))
  have hp := uniformPositive_strict _ (matrix_uniformPositive _ h) (flatten x) hx'
  change 0 < inner ℝ ((blockMatrix T.toLinearMap).toEuclideanLin (flatten x)) (flatten x) at hp
  rw [blockMatrix_action, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.inner_map_map] at hp
  exact hp

#print axioms uniformPositive_of_strict
#print axioms blockMatrix_uniformPositive
end LinearStochastic.PositiveFinite
