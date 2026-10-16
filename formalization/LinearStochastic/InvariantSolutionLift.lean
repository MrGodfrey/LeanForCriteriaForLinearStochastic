import LinearStochastic.InvariantAdjointDynamics
import LinearStochastic.SectionSolutionMap

/-! Lifting a genuine SDE solution on the invariant obstruction subspace
produces an actual backward adjoint solution with zero observation. -/
noncomputable section
namespace LinearStochastic.InvariantSolutionLift
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel LinearDuality SectionLinearDuality InvariantAdjointDynamics

section Algebra
variable {Λ E U ι : Type*} [mΛ : MeasurableSpace Λ] {ν : Measure Λ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U] [Fintype ι]
  (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
  (V : Submodule ℝ E) (d : Dynamics (ZeroObservationFlag.coefficients A B C D) V)

def liftedNoise (Q : Lp V 2 ν) (i : ι) : Lp E 2 ν :=
  V.subtypeL.compLp ((d.diffusion i).compLp Q)

omit [FiniteDimensional ℝ E] in
theorem liftedNoise_ae (Q : Lp V 2 ν) :
    ∀ᵐ z ∂ν, ∀ i, liftedNoise A B C D V d Q i z = (d.diffusion i (Q z) : E) := by
  rw [ae_all_iff]
  intro i
  filter_upwards [V.subtypeL.coeFn_compLp ((d.diffusion i).compLp Q),
    (d.diffusion i).coeFn_compLp Q] with z hi hg
  change V.subtypeL.compLp ((d.diffusion i).compLp Q) z = _
  rw [hi,hg]
  rfl

omit [FiniteDimensional ℝ E] in
/-- The observation vanishes as an actual predictable L² equivalence class. -/
theorem observation_zero (Q : Lp V 2 ν) :
    B.adjoint.compLp (V.subtypeL.compLp Q) +
      ∑ i, (D i).adjoint.compLp (liftedNoise A B C D V d Q i) = 0 := by
  apply Lp.ext
  filter_upwards [observation_ae B D (V.subtypeL.compLp Q) (liftedNoise A B C D V d Q),
    V.subtypeL.coeFn_compLp Q,liftedNoise_ae A B C D V d Q,Lp.coeFn_zero U 2 ν]
    with z ho hq hz h0
  rw [ho,hq,h0]
  simp only [hz,Submodule.subtypeL_apply,Pi.zero_apply]
  exact d.observation_zero (Q z)

omit [FiniteDimensional ℝ E] in
/-- The lifted drift is precisely the original backward adjoint drift,
including its minus sign and every channel term. -/
theorem drift_eq (Q : Lp V 2 ν) :
    V.subtypeL.compLp (d.drift.compLp Q) =
      -(A.adjoint.compLp (V.subtypeL.compLp Q) +
        ∑ i, (C i).adjoint.compLp (liftedNoise A B C D V d Q i)) := by
  apply Lp.ext
  filter_upwards [V.subtypeL.coeFn_compLp (d.drift.compLp Q),d.drift.coeFn_compLp Q,
    observation_ae A C (V.subtypeL.compLp Q) (liftedNoise A B C D V d Q),
    V.subtypeL.coeFn_compLp Q,liftedNoise_ae A B C D V d Q,
    Lp.coeFn_neg (A.adjoint.compLp (V.subtypeL.compLp Q) +
      ∑ i, (C i).adjoint.compLp (liftedNoise A B C D V d Q i))]
    with z hi hg ha hq hz hn
  rw [hi,hg,hn,Pi.neg_apply,ha,hq]
  simp only [hz,Submodule.subtypeL_apply]
  exact d.drift_eq (Q z)
end Algebra

section Stochastic
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι]
  (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
  (V : Submodule ℝ E) (d : Dynamics (ZeroObservationFlag.coefficients A B C D) V)
  (b : OrthonormalBasis κ ℝ V) (c : OrthonormalBasis τ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- A genuine integral solution on V lifts to the actual original backward
system. Existence of the input solution is an explicitly separate obligation. -/
theorem backward_solution (T : ℝ≥0) (ξ QT : Ω → V)
    (Q : Lp V 2 (spacetimeMeasure 𝓕 μ T))
    (hQ : SectionIntegralSolution b hW hWm T ξ (d.drift.compLp Q)
      (fun i => (d.diffusion i).compLp Q) Q QT) :
    SectionIntegralSolution c hW hWm T (fun ω => (ξ ω : E))
      (-(A.adjoint.compLp (V.subtypeL.compLp Q) +
        ∑ i, (C i).adjoint.compLp (liftedNoise (mΛ := 𝓕.predictable) A B C D V d Q i)))
      (liftedNoise (mΛ := 𝓕.predictable) A B C D V d Q) (V.subtypeL.compLp Q) (fun ω => (QT ω : E)) := by
  have h := SectionSolutionMap.SectionIntegralSolution.map b c hW hWm T V.subtypeL ξ
    (d.drift.compLp Q) (fun i => (d.diffusion i).compLp Q) Q QT hQ
  rw [drift_eq (mΛ := 𝓕.predictable) A B C D V d Q] at h
  exact h
end Stochastic

#print axioms backward_solution
end LinearStochastic.InvariantSolutionLift
