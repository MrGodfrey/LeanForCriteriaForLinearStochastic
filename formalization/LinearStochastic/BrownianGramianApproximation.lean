import LinearStochastic.KnownTargetLpReaching
import LinearStochastic.BrownianDelayedTarget
import LinearStochastic.RawControlProperties
import LinearStochastic.DeterministicGramianMatrices

/-! The manuscript's actual delayed conditional-expectation/Gramian proof
of approximate controllability in the zero-diffusion case. -/
noncomputable section
namespace LinearStochastic.BrownianGramianApproximation
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal
open CommonItoMultichannel ProgressiveControlSection
variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)
  (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (hK : ∀ v : E, (∀ k : ℕ, B.adjoint ((A.adjoint^k) v)=0) → v=0)

include hK in
/-- Every positive remaining horizon realizes the actual conditional target
with a finite-energy ordinary progressive control, zero on the whole prefix. -/
theorem delayed_reachable (T h : ℝ≥0) (hh : 0<h) (hT : h<T) (x : E) (η : Lp E 2 μ) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      fun i => JointUsualBrownianGlobal.coordinateForward hW hWm hInd i
    ∃ (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
      (u : Lp U 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T))
      (X : Lp E 2 (spacetimeMeasure (JointUsualNatural.usual (μ:=μ) W hWm) μ T)),
      RawSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T (fun _=>x) A B (fun _=>0) (fun _=>0) v R u X ∧
      R T =ᵐ[μ] BrownianDelayedTarget.target hWm η (T-h) ∧
      (∀ t, t≤T-h → ∀ ω, v t ω=0) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    fun i => JointUsualBrownianGlobal.coordinateForward hW hWm hInd i
  exact KnownTargetLpReaching.exists_solution b (fun i => (hW i).toIsPreBrownianReal) hWm
    A B (T-h) T (tsub_lt_self (hh.trans hT) hh) hK x _ (BrownianDelayedTarget.target_measurable hWm η (T-h))

include hK in
/-- The delayed targets converge, and the concrete finite-energy Gramian
controls therefore give the paper's expected-square-error approximation. -/
theorem approximate (T : ℝ≥0) (hT : 0<T) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      fun i => JointUsualBrownianGlobal.coordinateForward hW hWm hInd i
    RawControlProperties.Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      b hW hWm T A B (fun _=>0) (fun _=>0) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    fun i => JointUsualBrownianGlobal.coordinateForward hW hWm hInd i
  intro x η hη ε hε
  have hc := BrownianDelayedTarget.delayed_tendsto hW hWm hInd b T η hη
  have he : Tendsto (fun h : ℝ≥0 => ‖BrownianDelayedTarget.target hWm η (T-h)-η‖^2)
      (𝓝 0) (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_pow (by decide : 2≠0)] using (hc.sub (tendsto_const_nhds (x:=η))).norm.pow 2
  have hgood : ∀ᶠ h : ℝ≥0 in 𝓝 0,
      ‖BrownianDelayedTarget.target hWm η (T-h)-η‖^2<ε ∧ h<T :=
    (he.eventually (eventually_lt_nhds hε)).and (eventually_lt_nhds hT)
  have hg' : {h : ℝ≥0 | ‖BrownianDelayedTarget.target hWm η (T-h)-η‖^2<ε ∧ h<T} ∈ 𝓝[>] (0:ℝ≥0) :=
    mem_nhdsWithin_of_mem_nhds hgood
  obtain ⟨δ,hδ,hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hg'
  obtain ⟨h,hh,hhd⟩ := exists_between (show (0:ℝ≥0)<δ from hδ)
  obtain ⟨herr,hhT⟩ := hsub ⟨hh,hhd⟩
  obtain ⟨v,R,u,X,hsol,hterm,hzero⟩ := delayed_reachable b hW hWm hInd A B hK T h hh hhT x η
  refine ⟨v,R,u,X,hsol,?_⟩
  have heq : (∫ ω, ‖R T ω-η ω‖^2 ∂μ) = ‖BrownianDelayedTarget.target hWm η (T-h)-η‖^2 := by
    rw [ActualControlProperties.norm_error_sq]
    apply integral_congr_ae
    filter_upwards [hterm] with ω hω
    rw [hω]
  exact heq.trans_lt herr

end LinearStochastic.BrownianGramianApproximation

namespace LinearStochastic.BrownianGramianApproximation
open MeasureTheory ProbabilityTheory
open scoped NNReal
open ZeroObservationMatrices
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] [Fintype ι]
  {W : ι → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)

/-- The literal finite Kalman rank test implies AC by the fully constructed
delayed-target Gramian proof, independently of the abstract classification. -/
theorem matrix_approximate {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (hK : (Deterministic.kalman A B n).rank=n) (T : ℝ≥0) (hT : 0<T) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      fun i => JointUsualBrownianGlobal.coordinateForward hW hWm hInd i
    RawControlProperties.Approximate (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm)
      (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm T (matrixMap A) (matrixMap B) (fun _=>0) (fun _=>0) :=
  approximate (EuclideanSpace.basisFun (Fin n) ℝ) hW hWm hInd (matrixMap A) (matrixMap B)
    (DeterministicGramianMatrices.observable_of_kalman_rank A B hK) T hT

end LinearStochastic.BrownianGramianApproximation
