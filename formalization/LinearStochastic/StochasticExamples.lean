import LinearStochastic.RawBrownianClassification
import LinearStochastic.AlgebraNonrobustTopology

/-! The concrete algebraic examples now apply to actual original Brownian
systems and ordinary progressive controls. This module covers AC and ANC;
it does not assume an unproved exact-null or exact-control classification. -/
noncomputable section
namespace LinearStochastic.StochasticExamples
open MeasureTheory ProbabilityTheory
open scoped NNReal
open ZeroObservationMatrices RawControlProperties NonrobustTopology
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete]

/-- Every member of the singular joint-diffusion family is actually AC and
ANC at every prescribed positive horizon, even when its stacked rank drops. -/
theorem singular_approximate {W : Fin 2 → ℝ≥0 → Ω → ℝ}
    (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
    (hInd : iIndepFun (fun i ω t => W i t ω) μ) (T : ℝ≥0) (hT : 0 < T) (ε : ℝ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) (EuclideanSpace.basisFun (Fin 1) ℝ)
      hW hWm T (matrixMap 0) (matrixMap Examples.SingularDiffusion.B)
      (fun _ => matrixMap 0) (fun i => matrixMap (Examples.SingularDiffusion.D ε i)) ∧
    ApproximateNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) (EuclideanSpace.basisFun (Fin 1) ℝ)
      hW hWm T (matrixMap 0) (matrixMap Examples.SingularDiffusion.B)
      (fun _ => matrixMap 0) (fun i => matrixMap (Examples.SingularDiffusion.D ε i)) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  have h := RawBrownianClassification.matrix_classification hW hWm hInd (by decide) T hT
    (0 : Matrix (Fin 1) (Fin 1) ℝ) Examples.SingularDiffusion.B
    (fun _ => 0) (Examples.SingularDiffusion.D ε)
  exact ⟨h.1.mpr (Examples.SingularDiffusion.flag_one ε),h.2.mpr (Examples.SingularDiffusion.flag_one ε)⟩

variable {m : ℕ} {W : Fin (m+1) → ℝ≥0 → Ω → ℝ}
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hInd : iIndepFun (fun i ω t => W i t ω) μ) (T : ℝ≥0)

/-- The set of all actual coefficient tuples having AC, on this fixed actual
Brownian probability space and at this fixed horizon. -/
def approximateLocus : Set (CoefficientSpace 2 1 (m+1)) :=
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  {s | Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) (EuclideanSpace.basisFun (Fin 2) ℝ)
      hW hWm T (matrixMap s.1) (matrixMap s.2.1)
      (fun i => matrixMap (s.2.2.1 i)) (fun i => matrixMap (s.2.2.2 i))}

def approximateNullLocus : Set (CoefficientSpace 2 1 (m+1)) :=
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  {s | ApproximateNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) (EuclideanSpace.basisFun (Fin 2) ℝ)
      hW hWm T (matrixMap s.1) (matrixMap s.2.1)
      (fun i => matrixMap (s.2.2.1 i)) (fun i => matrixMap (s.2.2.2 i))}

/-- The actual AC locus is exactly the already computed ordinary-matrix flag
locus; this equality includes both directions of the raw-control formulation. -/
theorem approximate_locus_eq (hT : 0 < T) :
    approximateLocus hW hWm hInd T = {s : CoefficientSpace 2 1 (m+1) |
      (AdjointCoefficients.fromMatrices s.1 s.2.1 s.2.2.1 s.2.2.2).flag 2 = ⊥} := by
  ext s
  exact (RawBrownianClassification.matrix_classification hW hWm hInd (Nat.succ_pos m) T hT
    s.1 s.2.1 s.2.2.1 s.2.2.2).1

theorem approximateNull_locus_eq (hT : 0 < T) :
    approximateNullLocus hW hWm hInd T = {s : CoefficientSpace 2 1 (m+1) |
      (AdjointCoefficients.fromMatrices s.1 s.2.1 s.2.2.1 s.2.2.2).flag 2 = ⊥} := by
  ext s
  exact (RawBrownianClassification.matrix_classification hW hWm hInd (Nat.succ_pos m) T hT
    s.1 s.2.1 s.2.2.1 s.2.2.2).2

/-- Along the manuscript perturbation family, actual AC and ANC both hold
exactly at ε=0, with any positive number of independent noise channels. -/
theorem nonrobust_family (hT : 0 < T) (ε : ℝ) :
    (coefficientFamily m ε ∈ approximateLocus hW hWm hInd T ↔ ε=0) ∧
    (coefficientFamily m ε ∈ approximateNullLocus hW hWm hInd T ↔ ε=0) := by
  rw [approximate_locus_eq hW hWm hInd T hT,approximateNull_locus_eq hW hWm hInd T hT]
  exact ⟨actual_flag_bot_iff m ε,actual_flag_bot_iff m ε⟩

/-- Actual ordinary-progressive AC and ANC are nonopen in coefficient space,
not merely a surrogate algebraic condition. -/
theorem loci_not_open (hT : 0 < T) :
    ¬IsOpen (approximateLocus hW hWm hInd T) ∧ ¬IsOpen (approximateNullLocus hW hWm hInd T) := by
  rw [approximate_locus_eq hW hWm hInd T hT,approximateNull_locus_eq hW hWm hInd T hT]
  exact ⟨actual_coefficient_flag_not_open m,actual_coefficient_flag_not_open m⟩

/-- No continuous fixed-size maximal-rank test of the original coefficients
can characterize either actual AC or actual ANC for these dimensions. -/
theorem no_continuous_rank_test (hT : 0 < T) (a b : ℕ)
    (M : CoefficientSpace 2 1 (m+1) → Matrix (Fin a) (Fin b) ℝ) (hM : Continuous M) :
    ¬(∀ s, (M s).rank = min a b ↔ s ∈ approximateLocus hW hWm hInd T) ∧
    ¬(∀ s, (M s).rank = min a b ↔ s ∈ approximateNullLocus hW hWm hInd T) := by
  rw [approximate_locus_eq hW hWm hInd T hT,approximateNull_locus_eq hW hWm hInd T hT]
  exact ⟨no_continuous_coefficient_rank_test m a b M hM,no_continuous_coefficient_rank_test m a b M hM⟩

end LinearStochastic.StochasticExamples
