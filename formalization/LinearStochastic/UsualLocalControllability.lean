import LinearStochastic.ActualApproximation
import LinearStochastic.GlobalObservationDuality
import LinearStochastic.BSDEHilbertLocal
import LinearStochastic.JointUsualRepresentation

/-! Actual approximation on the Brownian usual filtration when the true flag
vanishes. Only the backward construction's explicit local rate remains; forward
solutions and scalar martingale representation are already global theorems. -/
noncomputable section
namespace LinearStochastic.UsualLocalControllability
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel HilbertLocalSolution ActualReachableDensity
open JointCylinderGeneration

variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  (c : OrthonormalBasis τ ℝ U)
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)
  (hWc : ∀ i ω, Continuous fun t => W i t ω)

include c in
/-- The actual zero-initial reachable set is dense in the true F_T L² space.
No martingale-representation or solution-existence assertion is a premise. -/
theorem reachable_dense (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hb : BSDEMatrixPicard.rate T (coefficientMatrix b b A) (fun i => coefficientMatrix b b (C i)) < 1)
    (hflag : (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
      fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i
    Dense (relativeTerminals (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b hW hWm T A B C D :
      Set (lpMeas E ℝ (JointUsualNatural.usual (μ:=μ) W hWm T) 2 μ)) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i
  let hp := JointUsualIndependence.pairForward W hW hWm hInd hWc
  let hi := fun i j (hij : i ≠ j) => hInd.indepFun hij
  apply dense_of_annihilator_zero b hW hWm T A B C D
  intro η hη hAnn
  obtain ⟨ξ,hξ,hξ2,Y,Z,hY,⟨r⟩⟩ := BSDEHilbertLocal.exists_section_backward b hW hWm hWc
    hp hi i₀ T A C η hη (JointUsualRepresentation.represented W hW hWm hInd hWc T) hb
  have he := GlobalObservationDuality.annihilator_terminal_zero b c hW hWm hWc hp hi
    i₀ T hT A B C D ξ η hξ2 hξ Y Z hY r hflag hAnn
  exact Lp.ext (he.trans (Lp.coeFn_zero E 2 μ).symm)

include c in
/-- Every F₀ L² initial state and F_T L² target are connected to arbitrary
squared L² accuracy by an actual control and original coefficient equation,
whenever the true flag is zero and the stated backward time rate holds. -/
theorem approximation_from_initial (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hb : BSDEMatrixPicard.rate T (coefficientMatrix b b A) (fun i => coefficientMatrix b b (C i)) < 1)
    (hflag : (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥)
    (ξ : Ω → E) (hξ : StronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (η : Lp E 2 μ) (hη : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T] η μ)
    (ε : ℝ) (hε : 0 < ε) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
      fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i
    ∃ (u : Lp U 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T))
      (X : Lp E 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T)) (XT : Lp E 2 μ),
      SectionLinearDuality.SectionIntegralSolution b hW hWm T ξ (A.compLp X+B.compLp u)
        (fun i => (C i).compLp X+(D i).compLp u) X XT ∧ ‖XT-η‖^2 < ε := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (natural W hWm) μ :=
    fun i => JointNaturalForward.coordinateForward W hW hWm hInd i
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    fun i => JointUsualIndependence.coordinateForward W hW hWm hInd hWc i
  exact ActualApproximation.approximation_from_initial b c hW hWm hWc i₀ T A B C D
    (reachable_dense b c W hW hWm hInd hWc i₀ T hT A B C D hb hflag) ξ hξ hξ2 η hη ε hε

end LinearStochastic.UsualLocalControllability
