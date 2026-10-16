import LinearStochastic.SwitchingActualFeedback
import LinearStochastic.UniformSwitchingFamily

/-! A single deterministic switching gain works for all original F0 L²
initial variables on each short horizon, with coefficient-only uniform cost. -/
set_option maxHeartbeats 1500000
noncomputable section
namespace LinearStochastic.SwitchingFeedbackSmall
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
open CommonItoMultichannel FeedbackIntervalRestart SwitchingFeedbackFamily SwitchingTimeMesh
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

include i₀ hpair hchannels in
theorem for_family (T : ℝ≥0) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Family (T:ℝ) A B C D)
    (ξ : Ω → EuclideanSpace ℝ (Fin n)) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ) :
    ∃ (u : Lp (EuclideanSpace ℝ (Fin r)) 2 (spacetimeMeasure 𝓕 μ T))
      (X : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T))
      (R : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n)),
      ProgressiveControlSection.RawSolution (EuclideanSpace.basisFun (Fin n) ℝ)
        (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
        A.toEuclideanLin.toContinuousLinearMap B.toEuclideanLin.toContinuousLinearMap
        (fun i => (C i).toEuclideanLin.toContinuousLinearMap) (fun i => (D i).toEuclideanLin.toContinuousLinearMap)
        (SwitchingFeedbackIdentity.feedback T (fun j => (f.U j*(f.P j)⁻¹).toEuclideanLin.toContinuousLinearMap) R)
        R u X ∧ R T =ᵐ[μ] 0 ∧
      (∫ s in Set.Ioc 0 (T:ℝ), ∫ ω,
        ‖SwitchingFeedbackIdentity.feedback T (fun j => (f.U j*(f.P j)⁻¹).toEuclideanLin.toContinuousLinearMap)
          R s.toNNReal ω‖^2 ∂μ) ≤
        ((8/7:ℝ)*f.M^2*f.L^(2*f.p-1)/(T:ℝ)^(4*f.p-2))*(∫ ω, ‖ξ ω‖^2 ∂μ) := by
  let η : Initial (μ:=μ) (𝓕:=𝓕) (n:=n) (time T 0) := ⟨ξ,by
    convert hξ using 1
    simp only [time_zero],hξ2⟩
  obtain ⟨q⟩ := SwitchingDynamics.exists_run hW hWm T A B C D f η i₀ hpair hchannels hT hT1
  obtain ⟨g⟩ := SwitchingState.exists_state hW hWm T A B C D f η q i₀
  exact ⟨SwitchingControl.total hW hWm T A B C D f η q i₀,g.X,g.path,
    SwitchingActualFeedback.raw_solution hW hWm T A B C D f η q i₀ g hT hT1,
    SwitchingState.terminal_zero hW hWm T A B C D f η q i₀ g hT hT1,
    SwitchingActualFeedback.energy_bound hW hWm T A B C D f η q i₀ g hT hT1⟩

include i₀ hpair hchannels in
theorem uniform_gain (hm : 0 < m)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) :
    ∃ (c₀ : ℝ) (N : ℕ), 0 < c₀ ∧ 1 ≤ N ∧ ∀ (T : ℝ≥0), 0 < T → T ≤ 1 →
      ∃ K : ℕ → Matrix (Fin r) (Fin n) ℝ,
        (∀ s : ℝ≥0, s < T → ∃ M : ℝ, 0 ≤ M ∧ ∀ t, t ≤ s →
          ‖SwitchingGain.gain T (fun j => (K j).toEuclideanLin.toContinuousLinearMap) t‖ ≤ M) ∧
        ∀ (ξ : Ω → EuclideanSpace ℝ (Fin n)), StronglyMeasurable[𝓕 0] ξ → MemLp ξ 2 μ →
        ∃ (u : Lp (EuclideanSpace ℝ (Fin r)) 2 (spacetimeMeasure 𝓕 μ T))
          (X : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T))
          (R : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n)),
          ProgressiveControlSection.RawSolution (EuclideanSpace.basisFun (Fin n) ℝ)
            (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
            A.toEuclideanLin.toContinuousLinearMap B.toEuclideanLin.toContinuousLinearMap
            (fun i => (C i).toEuclideanLin.toContinuousLinearMap) (fun i => (D i).toEuclideanLin.toContinuousLinearMap)
            (SwitchingFeedbackIdentity.feedback T (fun j => (K j).toEuclideanLin.toContinuousLinearMap) R)
            R u X ∧ R T =ᵐ[μ] 0 ∧
          (∫ s in Set.Ioc 0 (T:ℝ), ∫ ω,
            ‖SwitchingFeedbackIdentity.feedback T (fun j => (K j).toEuclideanLin.toContinuousLinearMap)
              R s.toNNReal ω‖^2 ∂μ) ≤ (c₀/(T:ℝ)^N)*(∫ ω, ‖ξ ω‖^2 ∂μ) := by
  obtain ⟨p⟩ := UniformSwitchingFamily.exists_parameters hm A B C D hflag
  refine ⟨(8/7:ℝ)*p.M^2*p.L^(2*p.p-1),4*p.p-2,?_,?_,?_⟩
  · have hM : 0 < p.M := lt_of_lt_of_le zero_lt_one p.M_ge_one
    have hL : 0 < p.L := lt_of_lt_of_le zero_lt_one p.L_ge_one
    positivity
  · have := p.p_ge_one
    omega
  · intro T hT hT1
    let f := UniformSwitchingFamily.family A B C D p (T:ℝ) hT hT1
    refine ⟨fun j => f.U j*(f.P j)⁻¹,?_,?_⟩
    · exact fun s hs => SwitchingGain.prefix_bound T _ s hs
    · exact fun ξ hξ hξ2 => for_family hW hWm i₀ hpair hchannels A B C D T hT hT1 f ξ hξ hξ2

end LinearStochastic.SwitchingFeedbackSmall
