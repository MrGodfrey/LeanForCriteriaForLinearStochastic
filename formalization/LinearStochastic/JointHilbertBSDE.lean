module

public import LinearStochastic.BSDEAnnihilator
public import LinearStochastic.JointMartingaleRepresentation

@[expose] public section

/-! The local Hilbert backward solution and zero terminal-annihilator result
on the actual joint Brownian natural filtration. Martingale representation and
forward independence are discharged by their proved joint Brownian theorems. -/
noncomputable section
namespace LinearStochastic.JointHilbertBSDE
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
/-- Every square-integrable terminal value measurable for the actual joint
natural Brownian filtration has a genuine local Hilbert adjoint BSDE solution.
There is no martingale-representation or solution-existence premise. -/
theorem exists_section_backward (i₀ : ι) (T : ℝ≥0) (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E)
    (η : Lp E 2 μ) (hη : AEStronglyMeasurable[natural W hWm T] η μ)
    (hc : BSDEMatrixPicard.rate T (coefficientMatrix b b A)
      (fun i => coefficientMatrix b b (C i)) < 1) :
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i;
    ∃ (ξ : Ω → E), StronglyMeasurable[natural W hWm 0] ξ ∧ MemLp ξ 2 μ ∧
      ∃ (Y : Lp E 2 (spacetimeMeasure (natural W hWm) μ T))
        (Z : ι → Lp E 2 (spacetimeMeasure (natural W hWm) μ T)),
        SectionIntegralSolution b hW hWm T ξ
          (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y η ∧
        Nonempty (ContinuousRealization T ξ Y η) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i;
  exact BSDEHilbertLocal.exists_section_backward b hW hWm hWc
    (JointNaturalForward.pairForward W hW hWm hInd) (fun _ _ hij => hInd.indepFun hij)
    i₀ T A C η hη (JointMartingaleRepresentation.represented W hW hWm hInd hWc T) hc

include hWc in
/-- On the original joint natural Brownian filtration, vanishing of the actual
obstruction flag forces every genuine local terminal annihilator to vanish.
Both actual solution constructions and martingale representation are proved. -/
theorem terminal_annihilator_eq_zero [FiniteDimensional ℝ E]
    (c : OrthonormalBasis τ ℝ U) (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hf : CommonVectorPicard.rate (𝓕:=natural W hWm) (μ:=μ) T (coefficientMatrix b b A)
      (fun i => coefficientMatrix b b (C i)) < 1)
    (hb : BSDEMatrixPicard.rate T (coefficientMatrix b b A)
      (fun i => coefficientMatrix b b (C i)) < 1)
    (hflag : (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥)
    (η : Lp E 2 μ) (hη : AEStronglyMeasurable[natural W hWm T] η μ) :
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i;
    ActualObservationDuality.AnnihilatesForwardTerminals (𝓕:=natural W hWm)
      b hW hWm T A B C D η → η = 0 := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i;
  intro hAnn
  exact BSDEAnnihilator.terminal_annihilator_eq_zero b c hW hWm hWc
    (JointNaturalForward.pairForward W hW hWm hInd) (fun _ _ hij => hInd.indepFun hij)
    i₀ T hT A B C D hf hb (JointMartingaleRepresentation.represented W hW hWm hInd hWc T)
    hflag η hη hAnn

end LinearStochastic.JointHilbertBSDE
