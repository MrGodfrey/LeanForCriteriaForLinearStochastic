module

public import LinearStochastic.SwitchingTimeMesh
public import LinearStochastic.ProcessQuadraticInner

@[expose] public section

/-! Actual S² continuity identifies the terminal random variable from the
vanishing moments along the genuine switching mesh. -/
noncomputable section
namespace LinearStochastic.SwitchingTerminalLimit
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal InnerProductSpace
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem terminal_moment_zero (T : ℝ≥0) (R : ℝ≥0 → Ω → E)
    (hm : ∀ t, AEStronglyMeasurable (R t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (h2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ)
    (hseq : Tendsto (fun j => ∫ ω, ‖R (SwitchingTimeMesh.time T j) ω‖^2 ∂μ) atTop (𝓝 0)) :
    (∫ ω, ‖R T ω‖^2 ∂μ) = 0 := by
  let f : ℝ → ℝ := fun s => ∫ ω, ‖R (min s.toNNReal T) ω‖^2 ∂μ
  have hf : Continuous f := by
    simpa only [ContinuousLinearMap.id_apply,real_inner_self_eq_norm_sq] using
      ProcessQuadraticInner.continuous_expected_product_clamped T R hm hc h2
        (ContinuousLinearMap.id ℝ E) (ContinuousLinearMap.id ℝ E)
  have heq : (fun j => f (Switching.switchTime (T:ℝ) j)) =
      (fun j => ∫ ω, ‖R (SwitchingTimeMesh.time T j) ω‖^2 ∂μ) := by
    funext j
    rw [←SwitchingTimeMesh.coe_time T j]
    simp only [f,Real.toNNReal_coe,min_eq_left (SwitchingTimeMesh.time_le T j)]
  have hz := Switching.terminal_value_zero_of_continuous f (T:ℝ) hf.continuousAt (heq.symm ▸ hseq)
  simpa only [f,Real.toNNReal_coe,min_self] using hz

theorem terminal_ae_zero (T : ℝ≥0) (R : ℝ≥0 → Ω → E)
    (hm : ∀ t, AEStronglyMeasurable (R t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (h2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ) (hRT : MemLp (R T) 2 μ)
    (hseq : Tendsto (fun j => ∫ ω, ‖R (SwitchingTimeMesh.time T j) ω‖^2 ∂μ) atTop (𝓝 0)) :
    R T =ᵐ[μ] 0 := by
  have hi : Integrable (fun ω => ‖R T ω‖^2) μ := by
    simpa only [Real.norm_eq_abs,abs_norm] using hRT.norm.integrable_sq
  have hz := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg ‖R T ω‖) hi).mp
    (terminal_moment_zero T R hm hc h2 hseq)
  filter_upwards [hz] with ω hω
  apply norm_eq_zero.mp
  have hh : ‖R T ω‖^2 = 0 := hω
  nlinarith [norm_nonneg (R T ω)]

end LinearStochastic.SwitchingTerminalLimit
