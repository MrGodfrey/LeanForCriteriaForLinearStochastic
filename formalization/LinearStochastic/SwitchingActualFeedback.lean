import LinearStochastic.SwitchingState
import LinearStochastic.SwitchingFeedbackIdentity
import LinearStochastic.RawPathOfRepresentative

/-! The constructed full-horizon S² state uses the literal deterministic
switching gain. The feedback is an actual ordinary progressive L² process. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace LinearStochastic.SwitchingActualFeedback
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
open CommonItoMultichannel FeedbackIntervalRestart SwitchingFeedbackFamily SwitchingTimeMesh SwitchingDynamics
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n r m : ℕ} [Nonempty (Fin n)]
  {W : Fin m → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (T : ℝ≥0) (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
  (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
  (f : Family (T:ℝ) A B C D) (ξ₀ : Initial (μ:=μ) (𝓕:=𝓕) (n:=n) (time T 0))
  (q : Run hW hWm T A B C D f ξ₀) (i₀ : Fin m)
  (g : SwitchingState.State hW hWm T A B C D f ξ₀ q i₀)

 theorem control_is_feedback (hT : 0 < T) (hT1 : T ≤ 1) :
    (SwitchingControl.total hW hWm T A B C D f ξ₀ q i₀ : ℝ≥0 × Ω → EuclideanSpace ℝ (Fin r))
      =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ]
        Function.uncurry (SwitchingFeedbackIdentity.feedback T
          (fun j => (f.U j*(f.P j)⁻¹).toEuclideanLin.toContinuousLinearMap) g.path) := by
  apply SwitchingFeedbackIdentity.feedback_ae (EuclideanSpace.basisFun (Fin n) ℝ)
    (EuclideanSpace.basisFun (Fin r) ℝ) T hT _ _ g.X g.path g.representative
  intro j
  rw [SwitchingControl.recover_window hW hWm T A B C D f ξ₀ q i₀ hT hT1 j,
    (SwitchingState.agrees_on_piece hW hWm T A B C D f ξ₀ q i₀ g hT hT1 j).1]
  rfl

 theorem feedback_admissible (hT : 0 < T) (hT1 : T ≤ 1) :
    IsStronglyProgressive 𝓕 (SwitchingFeedbackIdentity.feedback T
      (fun j => (f.U j*(f.P j)⁻¹).toEuclideanLin.toContinuousLinearMap) g.path) ∧
    MemLp (Function.uncurry (SwitchingFeedbackIdentity.feedback T
      (fun j => (f.U j*(f.P j)⁻¹).toEuclideanLin.toContinuousLinearMap) g.path)) 2
      ((CommonItoCLM.timeMeasure_T T).prod μ) := by
  refine ⟨SwitchingFeedbackIdentity.feedback_progressive (EuclideanSpace.basisFun (Fin n) ℝ)
    (EuclideanSpace.basisFun (Fin r) ℝ) T _ g.path g.progressive,?_⟩
  exact (memLp_congr_ae (control_is_feedback hW hWm T A B C D f ξ₀ q i₀ g hT hT1)).mp
    (memLp_of_memLp_trim 𝓕.predictable_le_prod (Lp.memLp _))

 theorem raw_solution (hT : 0 < T) (hT1 : T ≤ 1) :
    ProgressiveControlSection.RawSolution (EuclideanSpace.basisFun (Fin n) ℝ)
      (fun i => (hW i).toIsPreBrownianReal) hWm T ξ₀.val
      A.toEuclideanLin.toContinuousLinearMap B.toEuclideanLin.toContinuousLinearMap
      (fun i => (C i).toEuclideanLin.toContinuousLinearMap) (fun i => (D i).toEuclideanLin.toContinuousLinearMap)
      (SwitchingFeedbackIdentity.feedback T (fun j => (f.U j*(f.P j)⁻¹).toEuclideanLin.toContinuousLinearMap) g.path)
      g.path (SwitchingControl.total hW hWm T A B C D f ξ₀ q i₀) g.X :=
  RawPathOfRepresentative.raw_solution (EuclideanSpace.basisFun (Fin n) ℝ)
    (fun i => (hW i).toIsPreBrownianReal) hWm T ξ₀.val
    A.toEuclideanLin.toContinuousLinearMap B.toEuclideanLin.toContinuousLinearMap
    (fun i => (C i).toEuclideanLin.toContinuousLinearMap) (fun i => (D i).toEuclideanLin.toContinuousLinearMap)
    _ g.path _ g.X (feedback_admissible hW hWm T A B C D f ξ₀ q i₀ g hT hT1).1
    (control_is_feedback hW hWm T A B C D f ξ₀ q i₀ g hT hT1)
    g.progressive g.continuous g.squareSup g.representative g.equation

 theorem energy_bound (hT : 0 < T) (hT1 : T ≤ 1) :
    (∫ s in Set.Ioc 0 (T:ℝ), ∫ ω,
      ‖SwitchingFeedbackIdentity.feedback T (fun j => (f.U j*(f.P j)⁻¹).toEuclideanLin.toContinuousLinearMap)
        g.path s.toNNReal ω‖^2 ∂μ) ≤
      ((8/7:ℝ)*f.M^2*f.L^(2*f.p-1)/(T:ℝ)^(4*f.p-2))*(∫ ω, ‖ξ₀.val ω‖^2 ∂μ) := by
  rw [←ExpectedStateEnergy.norm_sq_eq_integral T _ _
    (control_is_feedback hW hWm T A B C D f ξ₀ q i₀ g hT hT1)]
  exact SwitchingControl.paper_energy_bound hW hWm T A B C D f ξ₀ q i₀ hT hT1

end LinearStochastic.SwitchingActualFeedback
