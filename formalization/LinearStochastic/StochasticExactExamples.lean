module

public import LinearStochastic.RawCompleteClassification
public import LinearStochastic.StochasticExamples

@[expose] public section

/-! Exact-null and exact-control conclusions for both concrete manuscript
families, including the nonopen actual ENC locus. -/
noncomputable section
namespace LinearStochastic.StochasticExactExamples
open MeasureTheory ProbabilityTheory
open scoped NNReal
open ZeroObservationMatrices NonrobustTopology
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete]

/-- Every singular-family parameter has actual ENC, while actual EC holds
exactly away from the joint-rank singularity ε=0. -/
theorem singular_exact {W : Fin 2 → ℝ≥0 → Ω → ℝ}
    (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
    (hInd : iIndepFun (fun i ω t=>W i t ω) μ) (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    RawExactProperties.ExactNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin 1) ℝ) hW hWm T (matrixMap 0) (matrixMap Examples.SingularDiffusion.B)
      (fun _=>matrixMap 0) (fun i=>matrixMap (Examples.SingularDiffusion.D ε i)) ∧
    (RawExactProperties.Exact (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin 1) ℝ) hW hWm T (matrixMap 0) (matrixMap Examples.SingularDiffusion.B)
      (fun _=>matrixMap 0) (fun i=>matrixMap (Examples.SingularDiffusion.D ε i)) ↔ ε≠0) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  refine ⟨(RawCompleteClassification.exactNull_iff_flag hW hWm hInd (by decide) (by decide) T hT
    0 Examples.SingularDiffusion.B (fun _=>0) (Examples.SingularDiffusion.D ε)).mpr
      (Examples.SingularDiffusion.flag_one ε),?_⟩
  have h := RawCompleteClassification.exact_iff_flag_rank hW hWm hInd (by decide) (by decide) T hT
    (0 : Matrix (Fin 1) (Fin 1) ℝ) Examples.SingularDiffusion.B (fun _=>0) (Examples.SingularDiffusion.D ε)
  constructor
  · intro he hz
    have hr := (h.mp he).2
    subst ε
    rw [Examples.SingularDiffusion.joint_rank_zero] at hr
    norm_num at hr
  · intro hε
    exact h.mpr ⟨Examples.SingularDiffusion.flag_one ε,by simpa using Examples.SingularDiffusion.joint_rank_ne_zero ε hε⟩

variable {m : ℕ} {W : Fin (m+1) → ℝ≥0 → Ω → ℝ}
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hInd : iIndepFun (fun i ω t=>W i t ω) μ) (T : ℝ≥0)

/-- The actual ordinary-progressive exact-null-controllable coefficient locus. -/
def exactNullLocus : Set (CoefficientSpace 2 1 (m+1)) :=
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  {s | RawExactProperties.ExactNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin 2) ℝ) hW hWm T (matrixMap s.1) (matrixMap s.2.1)
      (fun i=>matrixMap (s.2.2.1 i)) (fun i=>matrixMap (s.2.2.2 i))}

theorem exactNull_locus_eq (hT : 0 < T) :
    exactNullLocus hW hWm hInd T={s : CoefficientSpace 2 1 (m+1) |
      (AdjointCoefficients.fromMatrices s.1 s.2.1 s.2.2.1 s.2.2.2).flag 2=⊥} := by
  ext s
  exact RawCompleteClassification.exactNull_iff_flag hW hWm hInd (by decide) (Nat.succ_pos m) T hT
    s.1 s.2.1 s.2.2.1 s.2.2.2

/-- The nonrobust family has actual ENC precisely at ε=0 and never has EC. -/
theorem nonrobust_exact (hT : 0 < T) (ε : ℝ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    (coefficientFamily m ε ∈ exactNullLocus hW hWm hInd T ↔ ε=0) ∧
    ¬RawExactProperties.Exact (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin 2) ℝ) hW hWm T
      (matrixMap Examples.Nonrobustness.A) (matrixMap Examples.Nonrobustness.B)
      (fun i=>matrixMap (Examples.Nonrobustness.C m ε i)) (fun _=>matrixMap 0) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  constructor
  · rw [exactNull_locus_eq hW hWm hInd T hT]
    exact actual_flag_bot_iff m ε
  · intro h
    have hd := (RawCompleteClassification.exact_iff_flag_rank hW hWm hInd (by decide)
      (Nat.succ_pos m) T hT Examples.Nonrobustness.A Examples.Nonrobustness.B
      (Examples.Nonrobustness.C m ε) (fun _=>0)).mp h
    have hz : (SurjectiveMatrices.stack (fun _ : Fin (m+1)=>(0 : Matrix (Fin 2) (Fin 1) ℝ))).rank=0 := by
      change (0 : Matrix (Fin (m+1)×Fin 2) (Fin 1) ℝ).rank=0
      exact Matrix.rank_zero
    have he := hd.2
    rw [hz] at he
    omega

/-- ENC itself is not open in the original coefficient topology. -/
theorem exactNull_not_open (hT : 0 < T) : ¬IsOpen (exactNullLocus hW hWm hInd T) := by
  rw [exactNull_locus_eq hW hWm hInd T hT]
  exact actual_coefficient_flag_not_open m

/-- Hence no continuous fixed-size maximal-rank test of the original
coefficients can characterize actual ENC in general. -/
theorem no_continuous_rank_test (hT : 0 < T) (a b : ℕ)
    (M : CoefficientSpace 2 1 (m+1) → Matrix (Fin a) (Fin b) ℝ) (hM : Continuous M) :
    ¬(∀ s, (M s).rank=min a b ↔ s ∈ exactNullLocus hW hWm hInd T) := by
  rw [exactNull_locus_eq hW hWm hInd T hT]
  exact no_continuous_coefficient_rank_test m a b M hM

end LinearStochastic.StochasticExactExamples
