import LinearStochastic.SectionExpectedEnergy
import LinearStochastic.IntegralEnergyDecay
import LinearStochastic.SectionTerminalSpace

/-! Actual exponential quadratic decay of a homogeneous stochastic equation.
The energy identity and differential inequality are proved from the SDE and
pointwise Lyapunov inequality, rather than assumed as stochastic premises. -/
noncomputable section
namespace LinearStochastic.SectionExponentialEnergy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel LinearDuality SectionLinearDuality ExpectedQuadraticGenerator
variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

theorem exponential_energy
    (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (T : ℝ≥0) (H A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (ρ : ℝ) (hH : H.IsSymmetric)
    (hq : ∀ x, (∑ i, inner ℝ (C i x) (H (C i x))) +
      2 * inner ℝ (A x) (H x) ≤ -ρ * inner ℝ x (H x))
    (ξ : Ω → E) (hξ : MemLp ξ 2 μ) (hξ0 : StronglyMeasurable[𝓕 0] ξ)
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (R : ℝ≥0 → Ω → E)
    (hX : SectionIntegralSolution b hW hWm T ξ (A.compLp X) (fun i => (C i).compLp X) X (R T))
    (hr : X =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R)
    (hi : R 0 =ᵐ[μ] ξ)
    (he : ∀ t, t ≤ T → R t =ᵐ[μ] integralState b hW hWm T ξ
      (A.compLp X) (fun i => (C i).compLp X) (t:ℝ))
    (hm : ∀ t, AEStronglyMeasurable (R t) μ)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (h2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ) :
    (∫ ω, inner ℝ (R T ω) (H (R T ω)) ∂μ) ≤
      (∫ ω, inner ℝ (ξ ω) (H (ξ ω)) ∂μ) * Real.exp (-ρ * (T:ℝ)) := by
  let e : ℝ → ℝ := fun s => ∫ ω, inner ℝ (R (min s.toNNReal T) ω) (H (R (min s.toNNReal T) ω)) ∂μ
  let q : ℝ → ℝ := fun s => generator (μ:=μ) R H A C (min s.toNNReal T)
  have hqcont : Continuous q := continuous_clamped T R hm hc h2 H A C
  have hinit : (∫ ω, inner ℝ (R 0 ω) (H (R 0 ω)) ∂μ) =
      ∫ ω, inner ℝ (ξ ω) (H (ξ ω)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hi] with ω hi
    rw [hi]
  have hei (t : ℝ) (ht : t ∈ Icc 0 (T:ℝ)) : e t = e 0 + ∫ s in (0:ℝ)..t, q s := by
    have ht' : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
    have he' := SectionExpectedEnergy.prefix_energy b hW hWm hpair hchannels T H A C hH
      ξ hξ hξ0 X R hX hr he hm hc h2 t.toNNReal ht'
    rw [Real.coe_toNNReal t ht.1,←hinit] at he'
    change (∫ ω, inner ℝ (R (min t.toNNReal T) ω) (H (R (min t.toNNReal T) ω)) ∂μ) =
      (∫ ω, inner ℝ (R (min (0:ℝ).toNNReal T) ω) (H (R (min (0:ℝ).toNNReal T) ω)) ∂μ) + _
    rw [min_eq_left ht',Real.toNNReal_zero,min_eq_left (show (0:ℝ≥0) ≤ T from zero_le),he',
      intervalIntegral.integral_of_le ht.1]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    dsimp [q]
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr (hs.2.trans ht.2))]
  have hbound (t : ℝ) (ht : t ∈ Ico 0 (T:ℝ)) : q t ≤ -ρ * e t := by
    have ht' : min t.toNNReal T ≤ T := min_le_right _ _
    have hs := SectionHorizonRestriction.section_restrict b hW hWm ht' ξ (R T) (R (min t.toNNReal T))
      (A.compLp X) X (fun i => (C i).compLp X) hX (he _ ht')
    have hm2 := SectionTerminalSpace.SectionIntegralSolution.terminal_memLp b hW hWm
      (min t.toNNReal T) ξ (R (min t.toNNReal T)) _ _ _ hs hξ
    exact generator_le R H A C ρ hq _ hm2
  have hd := IntegralEnergyDecay.decay_of_integral_identity e q ρ T T.coe_nonneg hqcont hei hbound
  simpa only [e,Real.toNNReal_coe,min_self,Real.toNNReal_zero,
    min_eq_left (show (0:ℝ≥0) ≤ T from zero_le),hinit] using hd

end LinearStochastic.SectionExponentialEnergy
