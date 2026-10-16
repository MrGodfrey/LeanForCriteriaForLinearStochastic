import LinearStochastic.TerminalSpikeEstimate
import LinearStochastic.ActualObservationBound

/-! Actual terminal spikes exclude exact controllability when the joint
controlled diffusion fails to be onto. This first theorem keeps the explicit
continuous-driver version; the next module transports it to original Brownian
versions without this intermediate pathwise hypothesis. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.ExactDiffusionNecessity
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal InnerProductSpace BigOperators Topology
open CommonItoMultichannel SectionLinearDuality HilbertLocalSolution
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

include hWc hpair hchannels in
/-- Genuine normalized spike estimates force a quantitative obstruction to
any observation lower bound on the same fixed terminal horizon. -/
theorem spike_obstruction (i₀ : ι) (a δ : ℝ≥0) (hδ : 0 < δ)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (q : ι → E) (hq : ∑ i, ‖q i‖^2 = 1) (hkernel : ∑ i, (D i).adjoint (q i) = 0)
    (hc : (δ:ℝ)*CommonPicardHorizon.matrixSize (coefficientMatrix b b (-A.adjoint)) < 1)
    (K : ℝ) (hK : 0 ≤ K)
    (hobs : ∀ (Y : Lp E 2 (spacetimeMeasure 𝓕 μ (a+δ))) (η : Lp E 2 μ)
      (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ (a+δ))),
      SectionIntegralSolution b (fun i ↦ (hW i).toIsPreBrownianReal) hWm (a+δ) 0
        (-(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (Z i))) Z Y η →
      ‖η‖ ≤ K*‖B.adjoint.compLp Y+∑ i, (D i).adjoint.compLp (Z i)‖) :
    1 ≤ (K*‖B.adjoint‖+Real.sqrt ((a+δ:ℝ≥0):ℝ)*‖A.adjoint‖)*TerminalSpikeState.factor b δ A C q+
      Real.sqrt (δ:ℝ)*‖∑ i, (C i).adjoint (q i)‖ := by
  obtain ⟨Y,η,hs,hY⟩ := TerminalSpikeState.exists_solution (𝓕:=𝓕) b (fun i ↦ (hW i).toIsPreBrownianReal)
    hWm hWc i₀ a δ hδ A C q hc
  let Z := TerminalSpikeNoise.noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ (a+δ) le_rfl q
  have hlower := TerminalSpikeEstimate.unit_lower b (fun i ↦ (hW i).toIsPreBrownianReal) hWm
    hpair hchannels i₀ a δ hδ A C q hq Y (η : Lp E 2 μ) hs
  have hupper := hobs Y (η : Lp E 2 μ) Z hs
  have hz : ∑ i, (D i).adjoint.compLp (Z i) = 0 :=
    TerminalSpikeNoise.observation_zero (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ (a+δ) le_rfl q D hkernel
  rw [hz,add_zero] at hupper
  have hη := hupper.trans (mul_le_mul_of_nonneg_left (B.adjoint.norm_compLp_le Y) hK)
  have hcoef : 0 ≤ K*‖B.adjoint‖+Real.sqrt ((a+δ:ℝ≥0):ℝ)*‖A.adjoint‖ :=
    add_nonneg (mul_nonneg hK (norm_nonneg _)) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hh := mul_le_mul_of_nonneg_left hY hcoef
  nlinarith

include c hWc hpair hchannels in
/-- Exact controllability of the actual equation implies surjectivity of the
full joint diffusion, proved by actual terminal spikes and open mapping. -/
theorem joint_surjective (i₀ : ι) (T : ℝ≥0) (hT : 0 < T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (hEC : ActualControlProperties.Exact (𝓕:=𝓕) b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T A B C D) :
    Function.Surjective (InputStructure.jointDiffusion (fun i ↦ (D i).toLinearMap)) := by
  by_contra hD
  obtain ⟨q,hq,hkernel⟩ := DiffusionKernelWitness.exists_unit_kernel D hD
  have hq' := DiffusionKernelWitness.sum_norm_sq_eq_one q hq
  obtain ⟨K,hK,hobs⟩ := ActualObservationBound.bound_of_exact b c hW hWm hpair hchannels i₀ T A B C D hEC
  let M := CommonPicardHorizon.matrixSize (coefficientMatrix b b (-A.adjoint))
  let G := ‖∑ i, (C i).adjoint (q i)‖
  let F : ℝ≥0 → ℝ := fun δ ↦
    (K*‖B.adjoint‖+Real.sqrt (T:ℝ)*‖A.adjoint‖)*TerminalSpikeState.factor b δ A C (fun i ↦ q i)+Real.sqrt (δ:ℝ)*G
  have hf : Tendsto F (𝓝 0) (𝓝 0) := by
    have hs : Tendsto (fun δ : ℝ≥0 ↦ Real.sqrt (δ:ℝ)) (𝓝 0) (𝓝 0) := by
      have hh : Continuous (fun δ : ℝ≥0 ↦ Real.sqrt (δ:ℝ)) := by fun_prop
      simpa only [NNReal.coe_zero,Real.sqrt_zero] using hh.continuousAt.tendsto (x:=0)
    have hh := ((TerminalSpikeState.factor_tendsto b A C (fun i ↦ q i)).const_mul
      (K*‖B.adjoint‖+Real.sqrt (T:ℝ)*‖A.adjoint‖)).add (hs.mul_const G)
    simpa only [mul_zero,zero_mul,zero_add] using hh
  have hsmall : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0, F δ < 1 :=
    (hf.eventually (gt_mem_nhds zero_lt_one)).filter_mono nhdsWithin_le_nhds
  have hm : Tendsto (fun δ : ℝ≥0 ↦ (δ:ℝ)*M) (𝓝 0) (𝓝 0) := by
    have hh : Continuous (fun δ : ℝ≥0 ↦ (δ:ℝ)*M) := by fun_prop
    simpa only [NNReal.coe_zero,zero_mul] using hh.continuousAt.tendsto (x:=0)
  have hcoeff : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0, (δ:ℝ)*M < 1 :=
    (hm.eventually (gt_mem_nhds zero_lt_one)).filter_mono nhdsWithin_le_nhds
  have htime : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0, δ < T := (gt_mem_nhds hT).filter_mono nhdsWithin_le_nhds
  have hpos : ∀ᶠ δ : ℝ≥0 in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ,hδ,ht,hc,hs⟩ := (hpos.and (htime.and (hcoeff.and hsmall))).exists
  let a := T-δ
  have ha : a+δ = T := tsub_add_cancel_of_le ht.le
  have hobs' : ∀ (Y : Lp E 2 (spacetimeMeasure 𝓕 μ (a+δ))) (η : Lp E 2 μ)
      (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ (a+δ))),
      SectionIntegralSolution b (fun i ↦ (hW i).toIsPreBrownianReal) hWm (a+δ) 0
        (-(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (Z i))) Z Y η →
      ‖η‖ ≤ K*‖B.adjoint.compLp Y+∑ i, (D i).adjoint.compLp (Z i)‖ := by
    rw [ha]
    exact fun Y η Z hh ↦ hobs 0 η stronglyMeasurable_zero MemLp.zero Y Z hh
  have hcontra := spike_obstruction b hW hWm hWc hpair hchannels i₀ a δ hδ A B C D
    (fun i ↦ q i) hq' hkernel hc K hK.le hobs'
  rw [ha] at hcontra
  exact (not_le_of_gt hs) hcontra
end LinearStochastic.ExactDiffusionNecessity
