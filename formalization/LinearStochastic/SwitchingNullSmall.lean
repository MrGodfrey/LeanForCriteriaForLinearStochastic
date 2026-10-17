module

public import LinearStochastic.SwitchingState
public import LinearStochastic.UniformSwitchingFamily
public import LinearStochastic.ActualControlProperties
public import LinearStochastic.SectionSolutionLinearity

@[expose] public section

/-! Actual exact null control on every short horizon, with one genuinely
coefficient-dependent polynomial cost and arbitrary original F0 L² initial
variables. All control and state witnesses are constructed from the SDE. -/
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.SwitchingNullSmall
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel LinearDuality SectionLinearDuality
open FeedbackIntervalRestart SwitchingFeedbackFamily SwitchingTimeMesh SwitchingDynamics
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n r m : ℕ} [Nonempty (Fin n)]
  {W : Fin m → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (i₀ : Fin m)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
  (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
  (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)

include i₀ hpair hchannels

theorem exists_null_for_family (T : ℝ≥0) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Family (T:ℝ) A B C D)
    (ξ : Ω → EuclideanSpace ℝ (Fin n)) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ) :
    ∃ (u : Lp (EuclideanSpace ℝ (Fin r)) 2 (spacetimeMeasure 𝓕 μ T))
      (X : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T)),
      SectionIntegralSolution (EuclideanSpace.basisFun (Fin n) ℝ)
        (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
        (A.toEuclideanLin.toContinuousLinearMap.compLp X+B.toEuclideanLin.toContinuousLinearMap.compLp u)
        (fun i => (C i).toEuclideanLin.toContinuousLinearMap.compLp X+(D i).toEuclideanLin.toContinuousLinearMap.compLp u)
        X (0 : Ω → EuclideanSpace ℝ (Fin n)) ∧
      ‖u‖^2 ≤ ((8/7:ℝ)*f.M^2*f.L^(2*f.p-1)/(T:ℝ)^(4*f.p-2))*(∫ ω, ‖ξ ω‖^2 ∂μ) := by
  let η : Initial (μ:=μ) (𝓕:=𝓕) (n:=n) (time T 0) := ⟨ξ,by
    convert hξ using 1
    simp only [time_zero],hξ2⟩
  obtain ⟨q⟩ := SwitchingDynamics.exists_run hW hWm T A B C D f η i₀ hpair hchannels hT hT1
  obtain ⟨g⟩ := SwitchingState.exists_state hW hWm T A B C D f η q i₀
  refine ⟨SwitchingControl.total hW hWm T A B C D f η q i₀,g.X,?_,?_⟩
  · exact SectionSolutionLinearity.SectionIntegralSolution.terminal_congr
      (EuclideanSpace.basisFun (Fin n) ℝ) (fun i => (hW i).toIsPreBrownianReal) hWm T
      ξ (g.path T) 0 _ g.X _ g.solution (SwitchingState.terminal_zero hW hWm T A B C D f η q i₀ g hT hT1).symm
  · exact SwitchingControl.paper_energy_bound hW hWm T A B C D f η q i₀ hT hT1

theorem uniform_cost (hm : 0 < m)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) :
    ∃ (c₀ : ℝ) (N : ℕ), 0 < c₀ ∧ 1 ≤ N ∧ ∀ (T : ℝ≥0), 0 < T → T ≤ 1 →
      ∀ (ξ : Ω → EuclideanSpace ℝ (Fin n)), StronglyMeasurable[𝓕 0] ξ → MemLp ξ 2 μ →
      ∃ (u : Lp (EuclideanSpace ℝ (Fin r)) 2 (spacetimeMeasure 𝓕 μ T))
        (X : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T)),
        SectionIntegralSolution (EuclideanSpace.basisFun (Fin n) ℝ)
          (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
          (A.toEuclideanLin.toContinuousLinearMap.compLp X+B.toEuclideanLin.toContinuousLinearMap.compLp u)
          (fun i => (C i).toEuclideanLin.toContinuousLinearMap.compLp X+(D i).toEuclideanLin.toContinuousLinearMap.compLp u)
          X (0 : Ω → EuclideanSpace ℝ (Fin n)) ∧
        ‖u‖^2 ≤ (c₀/(T:ℝ)^N)*(∫ ω, ‖ξ ω‖^2 ∂μ) := by
  obtain ⟨p⟩ := UniformSwitchingFamily.exists_parameters hm A B C D hflag
  refine ⟨(8/7:ℝ)*p.M^2*p.L^(2*p.p-1),4*p.p-2,?_,?_,?_⟩
  · have hM : 0 < p.M := lt_of_lt_of_le zero_lt_one p.M_ge_one
    have hL : 0 < p.L := lt_of_lt_of_le zero_lt_one p.L_ge_one
    positivity
  · have := p.p_ge_one
    omega
  · intro T hT hT1 ξ hξ hξ2
    exact exists_null_for_family hW hWm i₀ hpair hchannels A B C D T hT hT1
      (UniformSwitchingFamily.family A B C D p (T:ℝ) hT hT1) ξ hξ hξ2

theorem exactNull (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (hT1 : T ≤ 1)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) :
    ActualControlProperties.ExactNull (𝓕:=𝓕) (EuclideanSpace.basisFun (Fin n) ℝ)
      (fun i => (hW i).toIsPreBrownianReal) hWm T
      A.toEuclideanLin.toContinuousLinearMap B.toEuclideanLin.toContinuousLinearMap
      (fun i => (C i).toEuclideanLin.toContinuousLinearMap) (fun i => (D i).toEuclideanLin.toContinuousLinearMap) := by
  obtain ⟨c₀,N,_,_,hh⟩ := uniform_cost hW hWm i₀ hpair hchannels A B C D hm hflag
  intro v
  obtain ⟨u,X,hX,_⟩ := hh T hT hT1 (fun _ => v) stronglyMeasurable_const (memLp_const v)
  exact ⟨u,X,SectionSolutionLinearity.SectionIntegralSolution.terminal_congr
    (EuclideanSpace.basisFun (Fin n) ℝ) (fun i => (hW i).toIsPreBrownianReal) hWm T
    (fun _ => v) 0 (0 : Lp (EuclideanSpace ℝ (Fin n)) 2 μ) _ X _ hX
    (Lp.coeFn_zero (EuclideanSpace ℝ (Fin n)) 2 μ)⟩

end LinearStochastic.SwitchingNullSmall
