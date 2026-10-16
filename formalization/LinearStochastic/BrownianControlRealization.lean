import LinearStochastic.BrownianControlClassification
import LinearStochastic.HilbertBrownianRealization
import LinearStochastic.HilbertBrownianUniqueness

/-! Actual controls and continuous S² paths witnessing the paper's expected
squared terminal error, on the original Brownian usual filtration. -/
noncomputable section
namespace LinearStochastic.BrownianControlRealization
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace
open CommonItoMultichannel SectionLinearDuality ActualControlProperties
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)

include c in
/-- An actual original-equation progressive continuous S² path attains any
prescribed positive expected squared terminal accuracy at any positive time. -/
theorem approximate_path (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hflag : (ZeroObservationFlag.coefficients A B C D).flag (Module.finrank ℝ E) = ⊥)
    (v : E) (η : Lp E 2 μ) (hη : AEStronglyMeasurable[JointUsualNatural.usual (μ:=μ) W hWm T] η μ)
    (ε : ℝ) (hε : 0 < ε) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    ∃ (u : Lp U 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T))
      (X : Lp E 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T)) (R : ℝ≥0 → Ω → E),
      IsStronglyProgressive (JointUsualNatural.usual (μ:=μ) W hWm) R ∧
      (∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T)) ∧
      MemLp (ContinuousDoobL2.pathSup R T) 2 μ ∧
      ((X : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R) ∧
      (R 0 =ᵐ[μ] fun _ => v) ∧
      (∀ t, t ≤ T → R t =ᵐ[μ] LinearDuality.integralState b (fun i => (hW i).toIsPreBrownianReal) hWm T
        (fun _ => v) (A.compLp X+B.compLp u) (fun i => (C i).compLp X+(D i).compLp u) (t:ℝ)) ∧
      (∫ ω, ‖R T ω-η ω‖^2 ∂μ) < ε := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  have hac := (BrownianControlClassification.classification b c hW hWm hInd i₀ T hT A B C D).1.mpr hflag
  obtain ⟨u,X,XT,hX,herr⟩ := hac v η hη ε hε
  obtain ⟨R,hp,hc,h2,hrep,h0,hend,heq⟩ := HilbertBrownianRealization.exists_realization b c hW hWm
    i₀ T A B C D (fun _ => v) stronglyMeasurable_const (memLp_const v) u X XT hX
  refine ⟨u,X,R,hp,hc,h2,hrep,h0,heq,?_⟩
  have he : (∫ ω, ‖R T ω-η ω‖^2 ∂μ) = ‖XT-η‖^2 := by
    rw [norm_error_sq XT η]
    exact integral_congr_ae (hend.mono (fun ω hω => by dsimp only; rw [hω]))
  rw [he]
  exact herr

end LinearStochastic.BrownianControlRealization
