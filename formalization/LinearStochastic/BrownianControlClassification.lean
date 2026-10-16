import LinearStochastic.UsualControlClassification
import LinearStochastic.ControlDriverTransport
import LinearStochastic.JointUsualBrownianGlobal

/-! Full approximate/approximate-null classification on the original complete
probability space and the original Brownian usual filtration. No everywhere
path-continuity, representation, local-rate or solution-existence premise is
present; actual version transport preserves every control and terminal error. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BrownianControlClassification
open MeasureTheory ProbabilityTheory
open scoped NNReal
open ActualControlProperties CommonBrownianRepair
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)

include c in
/-- For every T>0, actual AC and actual ANC are each equivalent to the
vanishing of the true terminal flag, under the paper's Brownian assumptions. -/
theorem classification (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    (Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D ↔
      (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥) ∧
    (ApproximateNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D ↔
      (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (repaired hW i)
      (JointCylinderGeneration.natural (repaired hW) (repaired_measurable hW)) μ :=
    fun i => JointNaturalForward.coordinateForward (repaired hW)
      (fun j => (repaired_brownian hW j).toIsPreBrownianReal) (repaired_measurable hW)
      (repaired_independent hW hInd) i
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (repaired hW i)
      (JointUsualNatural.usual (μ:=μ) (repaired hW) (repaired_measurable hW)) μ :=
    fun i => JointUsualIndependence.coordinateForward (repaired hW)
      (fun j => (repaired_brownian hW j).toIsPreBrownianReal) (repaired_measurable hW)
      (repaired_independent hW hInd) (repaired_continuous hW) i
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (repaired hW i)
      (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    fun i => CommonBrownianRepair.repaired_forward hW i
  have hr := UsualControlClassification.classification b c (repaired hW)
    (fun i => (repaired_brownian hW i).toIsPreBrownianReal) (repaired_measurable hW)
    (repaired_independent hW hInd) (repaired_continuous hW) i₀ T hT A B C D
  have hf := UsualVersionFiltration.repaired_usual_eq hWm hW
  have hr' :
      (Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b
        (fun i => (repaired_brownian hW i).toIsPreBrownianReal) (repaired_measurable hW) T A B C D ↔
        (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥) ∧
      (ApproximateNull (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b
        (fun i => (repaired_brownian hW i).toIsPreBrownianReal) (repaired_measurable hW) T A B C D ↔
        (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥) := by
    simpa only [hf] using hr
  have he (i : ι) : ∀ᵐ ω ∂μ, ∀ t, W i t ω = repaired hW i t ω :=
    (hW i).mk_ae_forall_eq.mono (fun _ hω t => (hω t).symm)
  exact ⟨(ControlDriverTransport.approximate_iff (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b
      (fun i => (hW i).toIsPreBrownianReal) (fun i => (repaired_brownian hW i).toIsPreBrownianReal)
      hWm (repaired_measurable hW) he T A B C D).trans hr'.1,
    (ControlDriverTransport.approximateNull_iff (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b
      (fun i => (hW i).toIsPreBrownianReal) (fun i => (repaired_brownian hW i).toIsPreBrownianReal)
      hWm (repaired_measurable hW) he T A B C D).trans hr'.2⟩

end LinearStochastic.BrownianControlClassification
