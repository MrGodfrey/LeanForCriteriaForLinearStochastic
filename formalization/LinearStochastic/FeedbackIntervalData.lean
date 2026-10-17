module

public import LinearStochastic.MatrixFeedbackPath

@[expose] public section

/-! Data produced by the actual constant-feedback solution theorem. The
terminal square-integrability and adaptedness are proved, so this record can
be restarted using the full original sigma algebra at its endpoint. -/
noncomputable section
namespace LinearStochastic.FeedbackIntervalData
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel LinearDuality SectionLinearDuality MatrixGrowthBounds
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n r m : ℕ} [Nonempty (Fin n)]
  {W : Fin m → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

structure Data (T : ℝ≥0) (ρ : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin r) (Fin n) ℝ) (hP : P.PosDef)
    (ξ : Ω → EuclideanSpace ℝ (Fin n)) where
  X : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T)
  path : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n)
  progressive : IsStronglyProgressive 𝓕 path
  continuous : ∀ᵐ ω ∂μ, ContinuousOn (fun t => path t ω) (Iic T)
  squareSup : MemLp (ContinuousDoobL2.pathSup path T) 2 μ
  representative : X =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry path
  initial : path 0 =ᵐ[μ] ξ
  solution : SectionIntegralSolution (EuclideanSpace.basisFun (Fin n) ℝ)
    (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
    (A.toEuclideanLin.toContinuousLinearMap.compLp X +
      B.toEuclideanLin.toContinuousLinearMap.compLp ((U*P⁻¹).toEuclideanLin.toContinuousLinearMap.compLp X))
    (fun i => (C i).toEuclideanLin.toContinuousLinearMap.compLp X +
      (D i).toEuclideanLin.toContinuousLinearMap.compLp ((U*P⁻¹).toEuclideanLin.toContinuousLinearMap.compLp X)) X (path T)
  equation : ∀ t, t ≤ T → path t =ᵐ[μ] integralState (EuclideanSpace.basisFun (Fin n) ℝ)
    (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
    ((A+B*(U*P⁻¹)).toEuclideanLin.toContinuousLinearMap.compLp X)
    (fun i => (C i+D i*(U*P⁻¹)).toEuclideanLin.toContinuousLinearMap.compLp X) (t:ℝ)
  decay : ∀ t, t ≤ T → (∫ ω, ‖path t ω‖^2 ∂μ) ≤ conditionNumber P hP.isHermitian *
    Real.exp (-ρ*(t:ℝ)) * (∫ ω, ‖ξ ω‖^2 ∂μ)
  controlEnergy : ‖(U*P⁻¹).toEuclideanLin.toContinuousLinearMap.compLp X‖^2 ≤
    ‖(U*P⁻¹).toEuclideanLin.toContinuousLinearMap‖^2 *
    (conditionNumber P hP.isHermitian * (∫ ω, ‖ξ ω‖^2 ∂μ) / ρ)

variable [𝓕.IsComplete μ]

theorem exists_data (i₀ : Fin m)
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin r) (Fin n) ℝ)
    (hP : P.PosDef) (hneg : (-LMIMatrixCoordinates.matrixLMI A B C D ρ P U).PosDef)
    (ξ : Ω → EuclideanSpace ℝ (Fin n)) (hξ : MemLp ξ 2 μ) (hξ0 : StronglyMeasurable[𝓕 0] ξ) :
    Nonempty (Data (𝓕:=𝓕) hW hWm T ρ A B C D P U hP ξ) := by
  obtain ⟨X,R,hp,hc,h2,hr,hi,hs,he,hd,henergy⟩ := MatrixFeedbackPath.exists_decay hW hWm i₀
    hpair hchannels T ρ hρ A B C D P U hP hneg ξ hξ hξ0
  exact ⟨⟨X,R,hp,hc,h2,hr,hi,hs,he,hd,henergy⟩⟩

omit [𝓕.IsComplete μ] in
theorem terminal_memLp (T : ℝ≥0) (ρ : ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin r) (Fin n) ℝ) (hP : P.PosDef)
    (ξ : Ω → EuclideanSpace ℝ (Fin n)) (hξ : MemLp ξ 2 μ)
    (q : Data (𝓕:=𝓕) hW hWm T ρ A B C D P U hP ξ) : MemLp (q.path T) 2 μ :=
  SectionTerminalSpace.SectionIntegralSolution.terminal_memLp (EuclideanSpace.basisFun (Fin n) ℝ)
    (fun i => (hW i).toIsPreBrownianReal) hWm T ξ (q.path T) _ q.X _ q.solution hξ

end LinearStochastic.FeedbackIntervalData
