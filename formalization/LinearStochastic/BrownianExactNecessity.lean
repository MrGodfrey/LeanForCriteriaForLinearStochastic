import LinearStochastic.ExactDiffusionNecessity
import LinearStochastic.SectionDriverTransport
import LinearStochastic.JointUsualBrownianGlobal

/-! The joint-diffusion necessity theorem for the original Brownian paths,
without strengthening their almost-sure continuity to everywhere continuity. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.BrownianExactNecessity
open MeasureTheory ProbabilityTheory
open scoped NNReal
open CommonBrownianRepair ActualControlProperties
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

section Common
variable {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

include c hpair hchannels in
/-- For the original drivers, exact controllability forces the actual joint
controlled diffusion onto. All repaired-path and Itô identities are proved. -/
theorem joint_surjective (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hEC : Exact (𝓕:=𝓕) b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A B C D) :
    Function.Surjective (InputStructure.jointDiffusion (fun i ↦ (D i).toLinearMap)) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (repaired hW i) 𝓕 μ := repaired_forward hW
  have hEC' : Exact (𝓕:=𝓕) b (fun i ↦ (repaired_brownian hW i).toIsPreBrownianReal)
      (repaired_measurable hW) T A B C D := by
    intro v η hη
    obtain ⟨u,X,hX⟩ := hEC v η hη
    refine ⟨u,X,?_⟩
    exact SectionDriverTransport.solution b (fun i ↦ (hW i).toIsPreBrownianReal)
      (fun i ↦ (repaired_brownian hW i).toIsPreBrownianReal) hWm (repaired_measurable hW)
      (fun i ↦ (hW i).mk_ae_forall_eq.mono (fun _ he t ↦ (he t).symm)) T _ _ _ _ _ hX
  have hch : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ repaired hW i t ω) (fun ω t ↦ repaired hW j t ω) μ := by
    intro i j hij
    exact (hchannels i j hij).congr (repaired_paths_ae hW i).symm (repaired_paths_ae hW j).symm
  exact ExactDiffusionNecessity.joint_surjective b c (repaired_brownian hW) (repaired_measurable hW)
    (repaired_continuous hW) (repaired_pairForward hW hpair) hch i₀ T hT A B C D hEC'
end Common

variable [μ.IsComplete] (hInd : iIndepFun (fun i ω t ↦ W i t ω) μ)

include c in
/-- The necessity theorem on the original Brownian usual filtration, for every
positive prescribed horizon, with no extra representation or continuity input. -/
theorem usual_joint_surjective (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    Exact (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A B C D →
      Function.Surjective (InputStructure.jointDiffusion (fun i ↦ (D i).toLinearMap)) := by
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
    JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  exact joint_surjective b c hW hWm (JointUsualBrownianGlobal.pairForward hW hWm hInd)
    (fun i j hij ↦ hInd.indepFun hij) i₀ T hT A B C D
end LinearStochastic.BrownianExactNecessity
