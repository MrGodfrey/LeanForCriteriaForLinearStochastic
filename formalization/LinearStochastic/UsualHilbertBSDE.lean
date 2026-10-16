import LinearStochastic.BSDEAnnihilator
import LinearStochastic.JointUsualRepresentation

/-! The local Hilbert backward solution and zero terminal-annihilator result
on the actual usual augmentation of the joint Brownian filtration. Martingale representation and
forward independence are discharged by their proved joint Brownian theorems. -/
noncomputable section
namespace LinearStochastic.UsualHilbertBSDE
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open JointCylinderGeneration CommonItoMultichannel HilbertLocalSolution SectionLinearDuality

variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t))
  (hInd : iIndepFun (fun i ω t => W i t ω) μ)
  (hWc : ∀ i ω, Continuous fun t => W i t ω)

include hWc in
/-- Every square-integrable terminal value measurable for the actual usual joint
Brownian filtration has a genuine local Hilbert adjoint BSDE solution.
There is no martingale-representation or solution-existence premise. -/
theorem exists_section_backward (i₀ : ι) (T : ℝ≥0) (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E)
    (η : Lp E 2 μ) (hη : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T] η μ)
    (hc : BSDEMatrixPicard.rate T (coefficientMatrix b b A)
      (fun i => coefficientMatrix b b (C i)) < 1) :
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i;
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i;
    ∃ (ξ : Ω → E), StronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm 0] ξ ∧ MemLp ξ 2 μ ∧
      ∃ (Y : Lp E 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T))
        (Z : ι → Lp E 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T)),
        SectionIntegralSolution b hW hWm T ξ
          (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y η ∧
        Nonempty (ContinuousRealization T ξ Y η) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i;
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i;
  exact BSDEHilbertLocal.exists_section_backward b hW hWm hWc
    (JointUsualIndependence.pairForward W hW hWm hInd hWc) (fun _ _ hij => hInd.indepFun hij)
    i₀ T A C η hη (JointUsualRepresentation.represented W hW hWm hInd hWc T) hc

include hWc in
/-- On the original usual joint Brownian filtration, vanishing of the actual
obstruction flag forces every genuine local terminal annihilator to vanish.
Both actual solution constructions and martingale representation are proved. -/
theorem terminal_annihilator_eq_zero [FiniteDimensional ℝ E]
    (c : OrthonormalBasis τ ℝ U) (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hf : CommonVectorPicard.rate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) (μ:=μ) T (coefficientMatrix b b A)
      (fun i => coefficientMatrix b b (C i)) < 1)
    (hb : BSDEMatrixPicard.rate T (coefficientMatrix b b A)
      (fun i => coefficientMatrix b b (C i)) < 1)
    (hflag : (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥)
    (η : Lp E 2 μ) (hη : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T] η μ) :
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i;
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i;
    ActualObservationDuality.AnnihilatesForwardTerminals (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      b hW hWm T A B C D η → η = 0 := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i;
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i;
  intro hAnn
  exact BSDEAnnihilator.terminal_annihilator_eq_zero b c hW hWm hWc
    (JointUsualIndependence.pairForward W hW hWm hInd hWc) (fun _ _ hij => hInd.indepFun hij)
    i₀ T hT A B C D hf hb (JointUsualRepresentation.represented W hW hWm hInd hWc T)
    hflag η hη hAnn

end LinearStochastic.UsualHilbertBSDE
