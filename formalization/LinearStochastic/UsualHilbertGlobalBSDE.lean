module

public import LinearStochastic.BSDEHilbertGlobal
public import LinearStochastic.UsualGlobalBSDE

@[expose] public section

/-! Actual arbitrary-horizon Hilbert adjoint existence on the original usual
Brownian filtration. All scalar martingale representation and backward SDE
existence are proved upstream, not assumed by this theorem. -/
noncomputable section
namespace LinearStochastic.UsualHilbertGlobalBSDE
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel HilbertLocalSolution SectionLinearDuality
open JointCylinderGeneration

variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)
  (hWc : ∀ i ω, Continuous fun t => W i t ω)

/-- Every positive horizon and original square-integrable measurable terminal
value have the genuine original adjoint solution and continuous realization. -/
theorem exists_section_backward (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E)
    (η : Lp E 2 μ) (hη : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T] η μ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
      fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i
    ∃ (ξ : Ω → E), StronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm 0] ξ ∧ MemLp ξ 2 μ ∧
      ∃ (Y : Lp E 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T))
        (Z : ι → Lp E 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T)),
        SectionIntegralSolution b hW hWm T ξ
          (-(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (Z i))) Z Y η ∧
        Nonempty (ContinuousRealization T ξ Y η) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i
  have hηc (j : κ) : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T]
      (VectorItoProduct.coordinate b j η) μ :=
    ((innerSL ℝ (b j)).continuous.comp_aestronglyMeasurable hη).congr
      (VectorItoProduct.coordinate_ae b j η).symm
  obtain ⟨q⟩ := UsualGlobalBSDE.exists_global W hW hWm hInd hWc i₀ T hT
    (coefficientMatrix b b A) (fun i => coefficientMatrix b b (C i))
    (fun j => VectorItoProduct.coordinate b j η) hηc
  exact BSDEHilbertGlobal.section_backward b hW hWm T A C η q

end LinearStochastic.UsualHilbertGlobalBSDE
