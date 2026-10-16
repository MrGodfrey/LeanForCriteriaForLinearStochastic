import LinearStochastic.RawRankClassification
import LinearStochastic.MatrixExactTerminal
import LinearStochastic.BrownianExactNecessity
import LinearStochastic.SwitchingNullAll

/-! The complete controllability classification for the original Brownian
usual filtration, ordinary progressive controls and actual continuous S²
solutions. No ENC, representation, small-time or driver-continuity premise is
left in the exact-controllability sufficiency direction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.RawCompleteClassification
open MeasureTheory ProbabilityTheory
open scoped NNReal
open ZeroObservationMatrices
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] {n r m : ℕ}
  {W : Fin m → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t=>W i t ω) μ)

/-- On every positive horizon, actual raw exact null controllability is
precisely the literal n-step algebraic obstruction test. -/
theorem exactNull_iff_flag (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    RawExactProperties.ExactNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ↔
      (AdjointCoefficients.fromMatrices A B C D).flag n=⊥ := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let c := EuclideanSpace.basisFun (Fin r) ℝ
  have he := RawExactProperties.exactNull_iff (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b c hW hWm T (matrixMap A) (matrixMap B)
    (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ⟨0,hm⟩
  constructor
  · intro h
    have hanc := ActualControlProperties.exactNull_implies_approximateNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b
      (fun i=>(hW i).toIsPreBrownianReal) hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) (he.mp h)
    have hr := (RawControlProperties.approximateNull_iff (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b c hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ⟨0,hm⟩).mpr hanc
    exact (RawBrownianClassification.matrix_classification hW hWm hInd hm T hT A B C D).2.mp hr
  · intro hflag
    exact he.mpr (SwitchingNullAll.exactNull hW hWm ⟨0,hm⟩
      (JointUsualBrownianGlobal.pairForward hW hWm hInd) (fun i j hij=>hInd.indepFun hij)
      A B C D hm T hT hflag)

/-- Exact controllability is equivalent to the obstruction test together
with the literal stacked diffusion matrix having full row rank. -/
theorem exact_iff_flag_rank (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    RawExactProperties.Exact (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ↔
      (AdjointCoefficients.fromMatrices A B C D).flag n=⊥ ∧ (SurjectiveMatrices.stack D).rank=m*n := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  let c := EuclideanSpace.basisFun (Fin r) ℝ
  have he := RawExactProperties.exact_iff (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b c hW hWm T (matrixMap A) (matrixMap B)
    (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ⟨0,hm⟩
  constructor
  · intro h
    have hnul := ActualControlProperties.exact_implies_exactNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b
      (fun i=>(hW i).toIsPreBrownianReal) hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) (he.mp h)
    have hraw := (RawExactProperties.exactNull_iff (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b c hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ⟨0,hm⟩).mpr hnul
    refine ⟨(exactNull_iff_flag hW hWm hInd hn hm T hT A B C D).mp hraw,?_⟩
    exact (SurjectiveMatrices.stack_full_rank_iff D).mpr
      (BrownianExactNecessity.usual_joint_surjective b c hW hWm hInd ⟨0,hm⟩ T hT
        (matrixMap A) (matrixMap B) (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) (he.mp h))
  · rintro ⟨hflag,hD⟩
    exact MatrixExactTerminal.matrix_exact_of_exactNull hW hWm hInd hm T hT A B C D hD
      ((exactNull_iff_flag hW hWm hInd hn hm T hT A B C D).mpr hflag)

/-- The main theorem, in the original raw control and path formulation:
AC, ANC and ENC share exactly one finite flag criterion, and EC additionally
requires the actual stacked diffusion matrix to have full row rank. -/
theorem classification (hn : 0 < n) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    (RawControlProperties.Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ↔
      (AdjointCoefficients.fromMatrices A B C D).flag n=⊥) ∧
    (RawControlProperties.ApproximateNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ↔
      (AdjointCoefficients.fromMatrices A B C D).flag n=⊥) ∧
    (RawExactProperties.ExactNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ↔
      (AdjointCoefficients.fromMatrices A B C D).flag n=⊥) ∧
    (RawExactProperties.Exact (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B)
      (fun i=>matrixMap (C i)) (fun i=>matrixMap (D i)) ↔
      (AdjointCoefficients.fromMatrices A B C D).flag n=⊥ ∧ (SurjectiveMatrices.stack D).rank=m*n) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  exact ⟨(RawBrownianClassification.matrix_classification hW hWm hInd hm T hT A B C D).1,
    (RawBrownianClassification.matrix_classification hW hWm hInd hm T hT A B C D).2,
    exactNull_iff_flag hW hWm hInd hn hm T hT A B C D,
    exact_iff_flag_rank hW hWm hInd hn hm T hT A B C D⟩

end LinearStochastic.RawCompleteClassification
