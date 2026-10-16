import LinearStochastic.SwitchingControl
import LinearStochastic.SwitchingTerminalLimit
import LinearStochastic.HilbertRestartUniqueness

/-! The genuine full-horizon S² solution driven by the constructed total
control agrees with every recursively solved interval. Its true terminal
random variable is zero, by the already proved moment limit and S² continuity. -/
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.SwitchingState
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel LinearDuality SectionLinearDuality
open FeedbackIntervalRestart SwitchingFeedbackFamily SwitchingTimeMesh SwitchingRates SwitchingDynamics
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n r m : ℕ} [Nonempty (Fin n)]
  {W : Fin m → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (T : ℝ≥0)
  (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
  (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
  (f : Family (T:ℝ) A B C D)
  (ξ₀ : Initial (μ:=μ) (𝓕:=𝓕) (n:=n) (time T 0))

variable (q : Run hW hWm T A B C D f ξ₀)

variable (i₀ : Fin m)

local instance shiftedForwardFamily (s : ℝ≥0) :
    ∀ i, CommonItoIsometry.ForwardIndependent (fun t ω => W i (s+t) ω-W i s ω)
      (CommonTimeShift.filtration 𝓕 s) μ := fun _ => CommonTimeShift.forwardIndependent s

omit [𝓕.IsComplete μ] [IsProbabilityMeasure μ] [Nonempty (Fin n)] in
theorem initial_measurable : StronglyMeasurable[𝓕 0] ξ₀.val := by
  convert ξ₀.property.1 using 1
  simp only [time_zero]

structure State where
  X : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T)
  path : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n)
  progressive : IsStronglyProgressive 𝓕 path
  continuous : ∀ᵐ ω ∂μ, ContinuousOn (fun t => path t ω) (Iic T)
  squareSup : MemLp (ContinuousDoobL2.pathSup path T) 2 μ
  representative : X =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry path
  initial : path 0 =ᵐ[μ] ξ₀.val
  solution : SectionIntegralSolution (EuclideanSpace.basisFun (Fin n) ℝ)
    (fun i => (hW i).toIsPreBrownianReal) hWm T ξ₀.val
    (A.toEuclideanLin.toContinuousLinearMap.compLp X+
      B.toEuclideanLin.toContinuousLinearMap.compLp (SwitchingControl.total hW hWm T A B C D f ξ₀ q i₀))
    (fun i => (C i).toEuclideanLin.toContinuousLinearMap.compLp X+
      (D i).toEuclideanLin.toContinuousLinearMap.compLp (SwitchingControl.total hW hWm T A B C D f ξ₀ q i₀)) X (path T)
  equation : ∀ t, t ≤ T → path t =ᵐ[μ] integralState (EuclideanSpace.basisFun (Fin n) ℝ)
    (fun i => (hW i).toIsPreBrownianReal) hWm T ξ₀.val
    (A.toEuclideanLin.toContinuousLinearMap.compLp X+
      B.toEuclideanLin.toContinuousLinearMap.compLp (SwitchingControl.total hW hWm T A B C D f ξ₀ q i₀))
    (fun i => (C i).toEuclideanLin.toContinuousLinearMap.compLp X+
      (D i).toEuclideanLin.toContinuousLinearMap.compLp (SwitchingControl.total hW hWm T A B C D f ξ₀ q i₀)) (t:ℝ)

theorem exists_state : Nonempty (State hW hWm T A B C D f ξ₀ q i₀) := by
  obtain ⟨X,R,hp,hc,h2,hr,hi,hs,_,he⟩ := HilbertBrownianPath.exists_full_solution
    (EuclideanSpace.basisFun (Fin n) ℝ) (EuclideanSpace.basisFun (Fin r) ℝ) hW hWm i₀ T
    A.toEuclideanLin.toContinuousLinearMap B.toEuclideanLin.toContinuousLinearMap
    (fun i => (C i).toEuclideanLin.toContinuousLinearMap) (fun i => (D i).toEuclideanLin.toContinuousLinearMap)
    ξ₀.val (initial_measurable T ξ₀) ξ₀.property.2 (SwitchingControl.total hW hWm T A B C D f ξ₀ q i₀)
  exact ⟨⟨X,R,hp,hc,h2,hr,hi,hs,he⟩⟩

omit [𝓕.IsComplete μ] in
theorem piece_equation (j : ℕ) : ∀ t, t ≤ duration T j →
    (q.piece j).path t =ᵐ[μ] integralState (𝓕:=CommonTimeShift.filtration 𝓕 (time T j))
      (EuclideanSpace.basisFun (Fin n) ℝ) (fun i => ((hW i).shift (time T j)).toIsPreBrownianReal)
      (fun i => CommonShiftSimple.shiftedMeas (hWm i) (time T j)) (duration T j) (q.initials j).val
      (A.toEuclideanLin.toContinuousLinearMap.compLp (q.piece j).X+
        B.toEuclideanLin.toContinuousLinearMap.compLp (control hW hWm T A B C D f ξ₀ q j))
      (fun i => (C i).toEuclideanLin.toContinuousLinearMap.compLp (q.piece j).X+
        (D i).toEuclideanLin.toContinuousLinearMap.compLp (control hW hWm T A B C D f ξ₀ q j)) (t:ℝ) := by
  simpa only [SwitchingDynamics.control,←MatrixFeedbackPath.closed_loop_compLp] using (q.piece j).equation

variable (g : State hW hWm T A B C D f ξ₀ q i₀)

theorem one_restart (hT : 0 < T) (hT1 : T ≤ 1) (j : ℕ)
    (hj : g.path (time T j) =ᵐ[μ] (q.initials j).val) :
    VectorH2Extension.shift (EuclideanSpace.basisFun (Fin n) ℝ) (time T j) (duration T j) T
      (SwitchingControl.inside T j) g.X = (q.piece j).X ∧
    ∀ s, s ≤ duration T j → g.path (time T j+s) =ᵐ[μ] (q.piece j).path s := by
  have hη : StronglyMeasurable[(CommonTimeShift.filtration 𝓕 (time T j)) 0] (q.initials j).val := by
    change StronglyMeasurable[𝓕 (time T j+0)] (q.initials j).val
    convert (q.initials j).property.1 using 1
    simp
  exact HilbertRestartUniqueness.restart
    (EuclideanSpace.basisFun (Fin n) ℝ) (EuclideanSpace.basisFun (Fin r) ℝ) hW hWm i₀ T
    A.toEuclideanLin.toContinuousLinearMap B.toEuclideanLin.toContinuousLinearMap
    (fun i => (C i).toEuclideanLin.toContinuousLinearMap) (fun i => (D i).toEuclideanLin.toContinuousLinearMap)
    ξ₀.val (initial_measurable T ξ₀) ξ₀.property.2
    (SwitchingControl.total hW hWm T A B C D f ξ₀ q i₀) g.X (g.path T) g.solution
    (time T j) (duration T j) (SwitchingControl.inside T j) (q.initials j).val hη (q.initials j).property.2
    (control hW hWm T A B C D f ξ₀ q j) (q.piece j).X ((q.piece j).path (duration T j))
    (q.piece j).solution g.path (q.piece j).path g.equation
    (piece_equation hW hWm T A B C D f ξ₀ q j) hj
    (SwitchingControl.recover_window hW hWm T A B C D f ξ₀ q i₀ hT hT1 j)

theorem at_mesh (hT : 0 < T) (hT1 : T ≤ 1) :
    ∀ j, g.path (time T j) =ᵐ[μ] (q.initials j).val := by
  intro j
  induction j with
  | zero =>
    rw [q.initial_zero]
    have he : g.path (time T 0) = g.path 0 := congrArg g.path (time_zero T)
    have hea : g.path (time T 0) =ᵐ[μ] g.path 0 := Filter.Eventually.of_forall (fun ω => congrFun he ω)
    exact hea.trans g.initial
  | succ j ih =>
    have he := (one_restart hW hWm T A B C D f ξ₀ q i₀ g hT hT1 j ih).2 (duration T j) le_rfl
    rwa [next_time,←q.next] at he

theorem agrees_on_piece (hT : 0 < T) (hT1 : T ≤ 1) (j : ℕ) :
    VectorH2Extension.shift (EuclideanSpace.basisFun (Fin n) ℝ) (time T j) (duration T j) T
      (SwitchingControl.inside T j) g.X = (q.piece j).X ∧
    ∀ s, s ≤ duration T j → g.path (time T j+s) =ᵐ[μ] (q.piece j).path s :=
  one_restart hW hWm T A B C D f ξ₀ q i₀ g hT hT1 j (at_mesh hW hWm T A B C D f ξ₀ q i₀ g hT hT1 j)

theorem terminal_zero (hT : 0 < T) (hT1 : T ≤ 1) : g.path T =ᵐ[μ] 0 := by
  have hseq : (fun j => ∫ ω, ‖g.path (time T j) ω‖^2 ∂μ) = moment hW hWm T A B C D f ξ₀ q := by
    funext j
    exact integral_congr_ae ((at_mesh hW hWm T A B C D f ξ₀ q i₀ g hT hT1 j).fun_comp (fun x => ‖x‖^2))
  have hRT := SectionTerminalSpace.SectionIntegralSolution.terminal_memLp
    (EuclideanSpace.basisFun (Fin n) ℝ) (fun i => (hW i).toIsPreBrownianReal) hWm T
    ξ₀.val (g.path T) _ g.X _ g.solution ξ₀.property.2
  apply SwitchingTerminalLimit.terminal_ae_zero T g.path
    (fun t => ((g.progressive.stronglyAdapted t).mono (𝓕.le t)).aestronglyMeasurable)
    g.continuous g.squareSup hRT
  rw [hseq]
  exact SwitchingSummability.moment_tendsto_zero hW hWm T A B C D f ξ₀ q hT hT1

end LinearStochastic.SwitchingState
