module

public import LinearStochastic.HilbertLocalSolution
public import LinearStochastic.InvariantSolutionLift
public import LinearStochastic.ZeroObservationSeparation

@[expose] public section

/-! A genuinely constructed nonzero invariant obstruction on a positive
short horizon. Global extension to every prescribed horizon is separate. -/
noncomputable section
namespace LinearStochastic.LocalInvariantObstruction
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality InvariantAdjointDynamics
open ZeroObservationFlag HilbertLocalSolution

variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

include hWc in
/-- No SDE existence hypothesis occurs here: the actual positive horizon and
the nonzero zero-observation solution are constructed by the proved Picard map. -/
theorem exists_local_zero_observation (i₀ : ι)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hflag : (coefficients A B C D).flag (Module.finrank ℝ E) ≠ ⊥) :
    ∃ (T : ℝ≥0), 0 < T ∧ ∃ (v : E), v ≠ 0 ∧ ∃ (YT : Ω → E), MemLp YT 2 μ ∧
      ∃ (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)),
        SectionIntegralSolution b hW hWm T (fun _ => v)
          (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y YT ∧
        B.adjoint.compLp Y + ∑ i, (D i).adjoint.compLp (Z i) = 0 := by
  let s := coefficients A B C D
  let V := s.flag (Module.finrank ℝ E)
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hflag
  let v₀ : V := ⟨v,hv⟩
  obtain ⟨d⟩ := exists_terminal_dynamics s
  let bV := stdOrthonormalBasis ℝ V
  let c := stdOrthonormalBasis ℝ ℝ
  obtain ⟨T,hT,hc⟩ := CommonPicardHorizon.exists_positive_contraction_horizon
    (𝓕 := 𝓕) (μ := μ) (coefficientMatrix bV bV d.drift)
      (fun i => coefficientMatrix bV bV (d.diffusion i))
  obtain ⟨Q,QT,hQ,hQT,_⟩ := exists_section_solution bV c hW hWm hWc i₀ T d.drift
    (0 : ℝ →L[ℝ] V) d.diffusion (fun _ => (0 : ℝ →L[ℝ] V))
    (fun _ => v₀) stronglyMeasurable_const (memLp_const v₀)
    (0 : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) hc
  have hz : (0 : ℝ →L[ℝ] V).compLp (0 : Lp ℝ 2 (spacetimeMeasure 𝓕 μ T)) = 0 :=
    map_zero ((0 : ℝ →L[ℝ] V).compLpₗ 2 _)
  simp only [hz,add_zero] at hQ
  have hback := InvariantSolutionLift.backward_solution A B C D V d bV b hW hWm T
    (fun _ => v₀) QT Q hQ
  refine ⟨T,hT,v,hv0,(fun ω => (QT ω : E)),V.subtypeL.comp_memLp' hQT,
    V.subtypeL.compLp Q,InvariantSolutionLift.liftedNoise (mΛ := 𝓕.predictable) A B C D V d Q,hback,?_⟩
  exact InvariantSolutionLift.observation_zero (mΛ := 𝓕.predictable) A B C D V d Q

include hWc in
/-- An actual nonzero terminal flag therefore yields a strict positive L²
separation at a genuinely constructed positive horizon. This local statement
does not claim failure for every larger prescribed horizon. -/
theorem exists_positive_horizon_separation (i₀ : ι)
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hflag : (coefficients A B C D).flag (Module.finrank ℝ E) ≠ ⊥) :
    ∃ (T : ℝ≥0), 0 < T ∧ ∃ (v : E), v ≠ 0 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
        (XT : Ω → E) (hXT : MemLp XT 2 μ),
        SectionIntegralSolution b hW hWm T (fun _ => v) (A.compLp X + B.compLp u)
          (fun i => (C i).compLp X + (D i).compLp u) X XT → ε ≤ ‖hXT.toLp XT‖ := by
  obtain ⟨T,hT,v,hv,YT,hYT,Y,Z,hY,hobs⟩ := exists_local_zero_observation (𝓕 := 𝓕)
    b hW hWm hWc i₀ A B C D hflag
  obtain ⟨ε,hε,hsep⟩ := ZeroObservationSeparation.positive_terminal_distance b hW hWm
    hpair hchannels T A B C D v hv YT hYT Y Z hY hobs
  exact ⟨T,hT,v,hv,ε,hε,hsep⟩

#print axioms exists_positive_horizon_separation
end LinearStochastic.LocalInvariantObstruction
