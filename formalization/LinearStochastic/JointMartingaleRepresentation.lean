/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

The orthogonal-complement proof is adapted from MathFin MartingaleRepresentation
to the actual finite-channel Ito isometry on the original joint natural filtration.
-/
import LinearStochastic.JointStepTotality
import LinearStochastic.BSDEIntegralRange

noncomputable section
namespace LinearStochastic.JointMartingaleRepresentation
open MeasureTheory ProbabilityTheory JointDoleansMoments
open scoped NNReal BigOperators InnerProductSpace
theorem inner_eq_integral_mul {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f g : Lp ℝ 2 μ) : inner ℝ f g = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  simp [RCLike.inner_apply,mul_comm]

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t))
  (hInd : iIndepFun (fun i ω t => W i t ω) μ)
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointCylinderGeneration.natural W hWm) μ]

/-- The actual joint-natural terminal Ito isometry with all independence
proofs derived from the given independent Brownian coordinates. -/
abbrev integral (T : ℝ≥0) := BSDEIntegralRange.integral (𝓕 := JointCylinderGeneration.natural W hWm)
  hW hWm (JointNaturalForward.pairForward W hW hWm hInd)
  (fun _ _ hij => hInd.indepFun hij) T

theorem integral_mean_zero (T : ℝ≥0)
    (f : BSDEIntegralRange.ChannelH2 (ι := ι) (𝓕 := JointCylinderGeneration.natural W hWm) (μ := μ) T) :
    ∫ ω, integral W hW hWm hInd T f ω ∂μ = 0 := by
  have hm : AEStronglyMeasurable[JointCylinderGeneration.natural W hWm 0]
      (Lp.const 2 μ (1 : ℝ) : Ω → ℝ) μ :=
    ⟨Function.const Ω (1 : ℝ),stronglyMeasurable_const,Lp.coeFn_const 2 μ (1 : ℝ)⟩
  have he := BSDEIntegralRange.initial_integral_orthogonal hW hWm
    (JointNaturalForward.pairForward W hW hWm hInd) (fun _ _ hij => hInd.indepFun hij)
    T (Lp.const 2 μ (1 : ℝ)) hm f
  rw [inner_eq_integral_mul] at he
  refine (integral_congr_ae ?_).trans he
  filter_upwards [Lp.coeFn_const 2 μ (1 : ℝ)] with ω hω
  simp only [hω,Function.const_apply,one_mul]

/-- Orthogonality to the true Ito range, plus zero mean, kills the actual step
exponentials represented above. -/
theorem orthogonal_step (hWc : ∀ i ω, Continuous fun t => W i t ω)
    (T : ℝ≥0) (z : Lp ℝ 2 μ)
    (hz : z ∈ (LinearMap.range (integral W hW hWm hInd T).toLinearMap)ᗮ)
    (hz0 : ∫ ω, z ω ∂μ = 0)
    (s : ℕ → ℝ≥0) (hs : Monotone s) (v : ℕ → ι → ℝ) (N : ℕ) (hsN : s N = T) :
    ∫ ω, z ω * stepExp W s v N ω ∂μ = 0 := by
  obtain ⟨f,_,hf⟩ := JointStepRepresentation.step_mem_range W hW hWm hInd hWc T hs v N hsN.le
  let f' : BSDEIntegralRange.ChannelH2 (ι := ι) (𝓕 := JointCylinderGeneration.natural W hWm) (μ := μ) T :=
    WithLp.toLp 2 f
  have hf' : (fun ω => stepExp W s v N ω - 1) =ᵐ[μ] integral W hW hWm hInd T f' := hf
  have hmul : Integrable (fun ω => integral W hW hWm hInd T f' ω * z ω) μ :=
    (Lp.memLp _).integrable_mul (Lp.memLp z)
  have hi : ∫ ω, integral W hW hWm hInd T f' ω * z ω ∂μ = 0 := by
    rw [←inner_eq_integral_mul]
    exact (Submodule.mem_orthogonal _ z).mp hz _ (LinearMap.mem_range_self _ f')
  rw [integral_congr_ae (g := fun ω => integral W hW hWm hInd T f' ω * z ω + z ω)
    (by filter_upwards [hf'] with ω hω; rw [sub_eq_iff_eq_add.mp hω]; ring),
    integral_add hmul ((Lp.memLp z).integrable one_le_two),hi,hz0,add_zero]

/-- Actual finite-channel martingale representation for centered terminal
variables in the original joint Brownian natural sigma algebra. -/
theorem centered_mem_range (hWc : ∀ i ω, Continuous fun t => W i t ω)
    (T : ℝ≥0) (F : Lp ℝ 2 μ)
    (hFm : AEStronglyMeasurable[JointCylinderGeneration.natural W hWm T] F μ)
    (hF0 : ∫ ω, F ω ∂μ = 0) :
    F ∈ LinearMap.range (integral W hW hWm hInd T).toLinearMap := by
  haveI : CompleteSpace ↥(LinearMap.range (integral W hW hWm hInd T).toLinearMap) :=
    ((integral W hW hWm hInd T).isometry.isClosedEmbedding.isClosed_range).completeSpace_coe
  obtain ⟨y,hy,z,hz,hFyz⟩ :=
    (LinearMap.range (integral W hW hWm hInd T).toLinearMap).exists_add_mem_mem_orthogonal F
  obtain ⟨f,hf⟩ := id hy
  have hym : y ∈ lpMeas ℝ ℝ (JointCylinderGeneration.natural W hWm T) 2 μ := by
    rw [←hf]
    exact BSDEIntegralRange.integral_terminal_measurable hW hWm
      (JointNaturalForward.pairForward W hW hWm hInd) (fun _ _ hij => hInd.indepFun hij) T f
  have hy0 : ∫ ω, y ω ∂μ = 0 := by
    rw [←hf]
    exact integral_mean_zero W hW hWm hInd T f
  have hz0 : ∫ ω, z ω ∂μ = 0 := by
    have he := integral_congr_ae (show (F : Ω → ℝ) =ᵐ[μ] fun ω => y ω + z ω by
      rw [hFyz]; exact Lp.coeFn_add y z)
    rw [integral_add ((Lp.memLp y).integrable one_le_two) ((Lp.memLp z).integrable one_le_two),
      hy0,hF0,zero_add] at he
    exact he.symm
  have hzm : z ∈ lpMeas ℝ ℝ (JointCylinderGeneration.natural W hWm T) 2 μ := by
    rw [eq_sub_of_add_eq' hFyz.symm]
    exact sub_mem hFm hym
  have hz' : z = 0 := JointStepTotality.eq_zero_of_orthogonal_stepExp W hW hWm hWc T z
    (mem_lpMeas_iff_aestronglyMeasurable.mp hzm)
    (fun s hs v N _ hsN => orthogonal_step W hW hWm hInd hWc T z hz hz0 s hs v N hsN)
  rw [hFyz,hz',add_zero]
  exact hy

/-- Every actual joint-natural terminal L² variable has a genuine
initial-plus-constructed-Ito decomposition. No MR premise is assumed. -/
theorem represented (hWc : ∀ i ω, Continuous fun t => W i t ω)
    (T : ℝ≥0) (F : Lp ℝ 2 μ)
    (hFm : AEStronglyMeasurable[JointCylinderGeneration.natural W hWm T] F μ) :
    BSDEIntegralRange.Represented hW hWm (JointNaturalForward.pairForward W hW hWm hInd)
      (fun _ _ hij => hInd.indepFun hij) T F := by
  let c : ℝ := ∫ ω, F ω ∂μ
  let ξ : Lp ℝ 2 μ := c • Lp.const 2 μ (1 : ℝ)
  have hξ : (ξ : Ω → ℝ) =ᵐ[μ] fun _ => c := by
    filter_upwards [Lp.coeFn_smul c (Lp.const 2 μ (1 : ℝ)),Lp.coeFn_const 2 μ (1 : ℝ)]
      with ω hs hc
    exact hs.trans (by rw [Pi.smul_apply,hc]; simp)
  have hξm : AEStronglyMeasurable[JointCylinderGeneration.natural W hWm 0] ξ μ :=
    ⟨fun _ => c,stronglyMeasurable_const,hξ⟩
  have hξT : AEStronglyMeasurable[JointCylinderGeneration.natural W hWm T] ξ μ :=
    hξm.mono ((JointCylinderGeneration.natural W hWm).mono bot_le)
  have hsub : (F - ξ : Lp ℝ 2 μ) =ᵐ[μ] fun ω => F ω - c := by
    filter_upwards [Lp.coeFn_sub F ξ,hξ] with ω hs hc
    rw [hs,Pi.sub_apply,hc]
  have hzero : ∫ ω, (F - ξ) ω ∂μ = 0 := by
    rw [integral_congr_ae hsub,integral_sub ((Lp.memLp F).integrable one_le_two) (integrable_const c),
      integral_const,probReal_univ,one_smul]
    exact sub_self c
  have hmeas : F - ξ ∈ lpMeas ℝ ℝ (JointCylinderGeneration.natural W hWm T) 2 μ :=
    sub_mem hFm hξT
  obtain ⟨f,hf⟩ := centered_mem_range W hW hWm hInd hWc T (F - ξ)
    (mem_lpMeas_iff_aestronglyMeasurable.mp hmeas) hzero
  refine ⟨ξ,hξm,f,?_⟩
  change F = ξ + integral W hW hWm hInd T f
  change integral W hW hWm hInd T f = F - ξ at hf
  rw [hf]
  abel

end LinearStochastic.JointMartingaleRepresentation
