module

public import LinearStochastic.HilbertFeedbackExtension
public import LinearStochastic.SwitchingFeedbackSmall

@[expose] public section

/-! One deterministic locally bounded piecewise matrix gain at every positive
horizon, with actual ordinary-progressive finite-energy feedback and terminal
zero for every initial random variable known at the original time zero. -/
set_option maxHeartbeats 1500000
noncomputable section
namespace LinearStochastic.SwitchingFeedbackAll
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
open CommonItoMultichannel
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

local instance shiftedForwardFamily (a : ℝ≥0) :
    ∀ i, CommonItoIsometry.ForwardIndependent (fun t ω => W i (a+t) ω-W i a ω)
      (CommonTimeShift.filtration 𝓕 a) μ := fun _ => CommonTimeShift.forwardIndependent a

include i₀ hpair hchannels in
theorem exists_gain (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) :
    ∃ (a δ : ℝ≥0) (K : ℕ → Matrix (Fin r) (Fin n) ℝ), a + δ = T ∧ 0 < δ ∧ δ ≤ 1 ∧
      (∀ s : ℝ≥0, s < T → ∃ M : ℝ, 0 ≤ M ∧ ∀ t, t ≤ s →
        ‖ShiftedSwitchingGain.gain a δ (fun j => (K j).toEuclideanLin.toContinuousLinearMap) t‖ ≤ M) ∧
      ∀ (ξ : Ω → EuclideanSpace ℝ (Fin n)), StronglyMeasurable[𝓕 0] ξ → MemLp ξ 2 μ →
      ∃ (u : Lp (EuclideanSpace ℝ (Fin r)) 2 (spacetimeMeasure 𝓕 μ T))
        (X : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T))
        (R : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n)),
        ProgressiveControlSection.RawSolution (EuclideanSpace.basisFun (Fin n) ℝ)
          (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
          A.toEuclideanLin.toContinuousLinearMap B.toEuclideanLin.toContinuousLinearMap
          (fun i => (C i).toEuclideanLin.toContinuousLinearMap) (fun i => (D i).toEuclideanLin.toContinuousLinearMap)
          (ShiftedFeedbackIdentity.feedback a δ (fun j => (K j).toEuclideanLin.toContinuousLinearMap) R)
          R u X ∧ R T =ᵐ[μ] 0 := by
  let δ : ℝ≥0 := min T 1
  let a := T-δ
  have hδ : 0 < δ := lt_min hT zero_lt_one
  have hδ1 : δ ≤ 1 := min_le_right T 1
  have haδ : a + δ = T := tsub_add_cancel_of_le (min_le_left T 1)
  obtain ⟨p⟩ := UniformSwitchingFamily.exists_parameters hm A B C D hflag
  let f := UniformSwitchingFamily.family A B C D p (δ:ℝ) hδ hδ1
  refine ⟨a,δ,fun j => f.U j*(f.P j)⁻¹,haδ,hδ,hδ1,?_,?_⟩
  · intro s hs
    exact ShiftedSwitchingGain.prefix_bound a δ _ s (haδ.symm ▸ hs)
  · intro ξ hξ hξ2
    apply HilbertFeedbackExtension.exists_feedback (EuclideanSpace.basisFun (Fin n) ℝ)
      (EuclideanSpace.basisFun (Fin r) ℝ) hW hWm i₀ a δ T haδ
      A.toEuclideanLin.toContinuousLinearMap B.toEuclideanLin.toContinuousLinearMap
      (fun i => (C i).toEuclideanLin.toContinuousLinearMap) (fun i => (D i).toEuclideanLin.toContinuousLinearMap)
      _ ξ hξ hξ2
    intro η hη hη2
    obtain ⟨u,X,R,hR,hend,_⟩ := SwitchingFeedbackSmall.for_family
      (fun i => (hW i).shift a) (fun i => CommonShiftSimple.shiftedMeas (hWm i) a)
      i₀ (CommonShiftRepresentation.pair_shift hpair a)
      (CommonShiftRepresentation.channels_shift hchannels a) A B C D δ hδ hδ1 f η hη hη2
    exact ⟨u,X,R,hR,hend⟩

end LinearStochastic.SwitchingFeedbackAll
