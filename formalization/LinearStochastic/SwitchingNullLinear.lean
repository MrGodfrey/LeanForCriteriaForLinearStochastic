import LinearStochastic.SwitchingLinearSolutions
import LinearStochastic.SwitchingState
import LinearStochastic.UniformSwitchingFamily
import LinearStochastic.ActualControlProperties
import LinearStochastic.SectionSolutionLinearity

/-! Actual exact null control on every short horizon, with one genuinely
coefficient-dependent polynomial cost and arbitrary original F0 L² initial
variables. All control and state witnesses are constructed from the SDE. -/
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.SwitchingNullLinear
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

theorem exists_good (T : ℝ≥0) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Family (T:ℝ) A B C D) (x : EuclideanSpace ℝ (Fin n)) :
    ∃ (u : Lp (EuclideanSpace ℝ (Fin r)) 2 (spacetimeMeasure 𝓕 μ T))
      (X : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T)),
      SwitchingLinearSolutions.Good (EuclideanSpace.basisFun (Fin n) ℝ)
        (EuclideanSpace.basisFun (Fin r) ℝ) hW hWm T
        A.toEuclideanLin.toContinuousLinearMap B.toEuclideanLin.toContinuousLinearMap
        (fun i => (C i).toEuclideanLin.toContinuousLinearMap)
        (fun i => (D i).toEuclideanLin.toContinuousLinearMap)
        (fun j => (f.U j*(f.P j)⁻¹).toEuclideanLin.toContinuousLinearMap) x u X ∧
      ‖u‖^2 ≤ ((8/7:ℝ)*f.M^2*f.L^(2*f.p-1)/(T:ℝ)^(4*f.p-2))*‖x‖^2 := by
  let η : Initial (μ:=μ) (𝓕:=𝓕) (n:=n) (time T 0) := ⟨fun _ => x,stronglyMeasurable_const,memLp_const x⟩
  obtain ⟨q⟩ := SwitchingDynamics.exists_run hW hWm T A B C D f η i₀ hpair hchannels hT hT1
  obtain ⟨g⟩ := SwitchingState.exists_state hW hWm T A B C D f η q i₀
  refine ⟨SwitchingControl.total hW hWm T A B C D f η q i₀,g.X,⟨?_,?_⟩,?_⟩
  · exact SectionSolutionLinearity.SectionIntegralSolution.terminal_congr
      (EuclideanSpace.basisFun (Fin n) ℝ) (fun i => (hW i).toIsPreBrownianReal) hWm T
      (fun _ => x) (g.path T) 0 _ g.X _ g.solution
      (SwitchingState.terminal_zero hW hWm T A B C D f η q i₀ g hT hT1).symm
  · intro j
    rw [SwitchingControl.recover_window hW hWm T A B C D f η q i₀ hT hT1 j,
      (SwitchingState.agrees_on_piece hW hWm T A B C D f η q i₀ g hT hT1 j).1]
    rfl
  · simpa [η, integral_const, Measure.real] using
      SwitchingControl.paper_energy_bound hW hWm T A B C D f η q i₀ hT hT1

/-- The actual choice of null controls is proved linear by genuine feedback
uniqueness. Finite dimensionality then supplies continuity, and the exact
switching bound supplies the quantitative cost. -/
theorem continuous_linear_null_map (T : ℝ≥0) (hT : 0 < T) (hT1 : T ≤ 1)
    (f : Family (T:ℝ) A B C D) :
    ∃ F : EuclideanSpace ℝ (Fin n) →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin r)) 2 (spacetimeMeasure 𝓕 μ T),
      ∀ x, (∃ X, SwitchingLinearSolutions.Good (EuclideanSpace.basisFun (Fin n) ℝ)
        (EuclideanSpace.basisFun (Fin r) ℝ) hW hWm T
        A.toEuclideanLin.toContinuousLinearMap B.toEuclideanLin.toContinuousLinearMap
        (fun i => (C i).toEuclideanLin.toContinuousLinearMap)
        (fun i => (D i).toEuclideanLin.toContinuousLinearMap)
        (fun j => (f.U j*(f.P j)⁻¹).toEuclideanLin.toContinuousLinearMap) x (F x) X) ∧
      ‖F x‖^2 ≤ ((8/7:ℝ)*f.M^2*f.L^(2*f.p-1)/(T:ℝ)^(4*f.p-2))*‖x‖^2 := by
  choose u X hgood hbound using exists_good hW hWm i₀ hpair hchannels A B C D T hT hT1 f
  let F : EuclideanSpace ℝ (Fin n) →ₗ[ℝ]
      Lp (EuclideanSpace ℝ (Fin r)) 2 (spacetimeMeasure 𝓕 μ T) :=
    { toFun := u
      map_add' := fun x y => SwitchingLinearSolutions.control_unique
        (EuclideanSpace.basisFun (Fin n) ℝ) (EuclideanSpace.basisFun (Fin r) ℝ)
        hW hWm T _ _ _ _ _ i₀ hT (hgood (x+y))
        (SwitchingLinearSolutions.add_good _ _ _ _ _ _ _ _ _ _ (hgood x) (hgood y))
      map_smul' := fun a x => SwitchingLinearSolutions.control_unique
        (EuclideanSpace.basisFun (Fin n) ℝ) (EuclideanSpace.basisFun (Fin r) ℝ)
        hW hWm T _ _ _ _ _ i₀ hT (hgood (a • x))
        (SwitchingLinearSolutions.smul_good _ _ _ _ _ _ _ _ _ _ a (hgood x)) }
  exact ⟨F.toContinuousLinearMap,fun x => ⟨⟨X x,hgood x⟩,hbound x⟩⟩

end LinearStochastic.SwitchingNullLinear
