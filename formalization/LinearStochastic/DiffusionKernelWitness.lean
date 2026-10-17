module

public import LinearStochastic.InputStructure

@[expose] public section

/-! Failure of the actual joint diffusion map to be onto produces a genuine
unit vector killed by the sum of the channel adjoints. -/
noncomputable section
namespace LinearStochastic.DiffusionKernelWitness
open scoped InnerProductSpace BigOperators
variable {E U ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [Fintype ι]

/-- The normalized vector lives in the full channel product; individual
channel surjectivity is not substituted for joint surjectivity. -/
theorem exists_unit_kernel (D : ι → U →L[ℝ] E)
    (hD : ¬Function.Surjective (InputStructure.jointDiffusion (fun i ↦ (D i).toLinearMap))) :
    ∃ q : PiLp 2 (fun _ : ι ↦ E), ‖q‖ = 1 ∧ ∑ i, (D i).adjoint (q i) = 0 := by
  let J := InputStructure.jointDiffusion (fun i ↦ (D i).toLinearMap)
  have hk : J.adjoint.ker ≠ ⊥ := by
    intro he
    have ho : J.rangeᗮ = ⊥ := J.orthogonal_range.trans he
    exact hD (LinearMap.range_eq_top.mp ((Submodule.orthogonal_eq_bot_iff (K:=J.range)).mp ho))
  obtain ⟨q,hq,hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  let p := ‖q‖⁻¹ • q
  have hp : ‖p‖ = 1 := by
    simp only [p,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _)]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq0)
  refine ⟨p,hp,?_⟩
  have hz : J.adjoint p = 0 := by
    rw [map_smul]
    change ‖q‖⁻¹ • J.adjoint q = 0
    rw [LinearMap.mem_ker.mp hq,smul_zero]
  have he := InputStructure.jointDiffusion_adjoint_apply (fun i ↦ (D i).toLinearMap) p
  change J.adjoint p = _ at he
  rw [hz] at he
  simpa only [ContinuousLinearMap.adjoint_toLinearMap,ContinuousLinearMap.coe_coe] using he.symm

omit [FiniteDimensional ℝ E] in
/-- The Hilbert unit normalization is exactly the manuscript's sum of squared
Euclidean channel norms. -/
theorem sum_norm_sq_eq_one (q : PiLp 2 (fun _ : ι ↦ E)) (hq : ‖q‖ = 1) :
    ∑ i, ‖q i‖^2 = 1 := by
  have hh : inner ℝ q q = 1 := by rw [real_inner_self_eq_norm_sq,hq]; norm_num
  simpa only [PiLp.inner_apply,real_inner_self_eq_norm_sq] using hh
end LinearStochastic.DiffusionKernelWitness
