import LinearStochastic.ZeroObservationFlag
import LinearStochastic.InputStructure

/-! Construction of the genuine autonomous dynamics on an invariant
obstruction subspace from the algebraically proved linear selectors. -/
noncomputable section
namespace LinearStochastic.InvariantAdjointDynamics
open MeasureTheory
open scoped InnerProductSpace BigOperators

variable {E U ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [Fintype ι]

/-- Actual finite-dimensional drift and diffusion maps, together with their
literal coefficient equations. Existence is proved below from fixed-point
invariance, rather than postulated as a stochastic controllability premise. -/
structure Dynamics (s : AdjointCoefficients (𝕜 := ℝ) (E := E) (U := U) (ι := ι))
    (V : Submodule ℝ E) where
  drift : V →L[ℝ] V
  diffusion : ι → V →L[ℝ] V
  drift_eq : ∀ v : V, (drift v : E) = -(s.A v + ∑ i, s.C i (diffusion i v))
  observation_zero : ∀ v : V, s.B v + ∑ i, s.D i (diffusion i v) = 0

/-- Construct all coefficients on the actual invariant subspace by restricting
the proved global linear selectors; continuity follows from finite dimension. -/
theorem exists_dynamics (s : AdjointCoefficients (𝕜 := ℝ) (E := E) (U := U) (ι := ι))
    (V : Submodule ℝ E) (hV : s.obstruction V = V) : Nonempty (Dynamics s V) := by
  obtain ⟨Γ,hΓ⟩ := (s.fixed_iff_selectors V).mp hV
  let G : ι → V →ₗ[ℝ] V := fun i =>
    ((Γ i).comp V.subtype).codRestrict V (fun v => (hΓ v v.property).1 i)
  have hG (i : ι) (v : V) : (G i v : E) = Γ i v := rfl
  let L : V →ₗ[ℝ] E := -(s.A.comp V.subtype + ∑ i, (s.C i).comp (V.subtype.comp (G i)))
  have hL (v : V) : L v ∈ V := by
    simpa only [L,LinearMap.neg_apply,LinearMap.add_apply,LinearMap.sum_apply,
      LinearMap.comp_apply,Submodule.subtype_apply,hG] using V.neg_mem (hΓ v v.property).2.2
  refine ⟨⟨(L.codRestrict V hL).toContinuousLinearMap,
    fun i => (G i).toContinuousLinearMap,?_,?_⟩⟩
  · intro v
    simp [L,G]
  · intro v
    exact (hΓ v v.property).2.1

/-- The terminal obstruction always has genuine restricted linear dynamics. -/
theorem exists_terminal_dynamics
    (s : AdjointCoefficients (𝕜 := ℝ) (E := E) (U := U) (ι := ι)) :
    Nonempty (Dynamics s (s.flag (Module.finrank ℝ E))) := by
  apply exists_dynamics
  exact s.flag_stable_at_finrank

section Forward
variable [CompleteSpace E] [CompleteSpace U] [FiniteDimensional ℝ U]

omit [Fintype ι] in
/-- The continuous-adjoint coefficients used by the actual SDE interface are
exactly the earlier finite-dimensional forward-to-adjoint algebraic maps. -/
theorem coefficients_eq_fromForward (A : E →L[ℝ] E) (B : U →L[ℝ] E)
    (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E) :
    ZeroObservationFlag.coefficients A B C D =
      InputStructure.fromForward A.toLinearMap B.toLinearMap
        (fun i => (C i).toLinearMap) (fun i => (D i).toLinearMap) := by
  simp only [ZeroObservationFlag.coefficients,InputStructure.fromForward,
    ContinuousLinearMap.adjoint_toLinearMap]
end Forward

#print axioms exists_terminal_dynamics
end LinearStochastic.InvariantAdjointDynamics
