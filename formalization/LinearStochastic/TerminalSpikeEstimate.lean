import LinearStochastic.TerminalSpikeState
import LinearStochastic.TerminalDriftWindow

/-! Quantitative terminal estimates for actual normalized adjoint spikes. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.TerminalSpikeEstimate
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality HilbertLocalSolution PredictableConstant
open SectionTerminalSpace VectorItoNaturality TerminalSpikeState
variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- The separately specified endpoint equals the actual Lebesgue and Itô
terminal variables, as an equality of genuine L² elements. -/
theorem endpoint_eq (T : ℝ≥0) (Y f : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) (η : Lp E 2 μ)
    (hs : SectionIntegralSolution b hW hWm T 0 f Z Y η) :
    η = terminalDrift b T f+vectorLp b hW hWm T T Z := by
  apply Lp.ext
  filter_upwards [hs.terminal,terminalDrift_ae b T f,vectorProcess_ae_vectorLp b hW hWm T T Z,
    Lp.coeFn_add (terminalDrift b T f) (vectorLp b hW hWm T T Z)] with ω he hd hi ha
  simp only [LinearDuality.integralState,Real.toNNReal_coe,Pi.zero_apply,zero_add] at he
  rw [ha,Pi.add_apply,hd,←hi]
  exact he

/-- The C-dependent part of the adjoint drift remains the actual same window,
so its terminal drift costs sqrt δ rather than sqrt T. -/
theorem forcing_drift_bound (i₀ : ι) (a δ : ℝ≥0) (hδ : 0 < δ)
    (C : ι → E →L[ℝ] E) (q : ι → E) :
    ‖terminalDrift b (a+δ) (∑ i, (C i).adjoint.compLp
      (TerminalSpikeNoise.noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ (a+δ) le_rfl q i))‖ ≤
      Real.sqrt (δ:ℝ)*‖∑ i, (C i).adjoint (q i)‖ := by
  let L := windowLinear (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ (a+δ) le_rfl
  let g := ∑ i, (C i).adjoint (q i)
  have he : (∑ i, (C i).adjoint.compLp (TerminalSpikeNoise.noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ (a+δ) le_rfl q i)) = L g := by
    change _ = L (∑ i, (C i).adjoint (q i))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact VectorExtensionNaturality.normalized_constant (𝓕:=𝓕) (μ:=μ) b b (hWm i₀) a δ (a+δ) le_rfl (C i).adjoint (q i)
  rw [he]
  have hh := TerminalDriftWindow.terminalDrift_window_bound (𝓕:=𝓕) (hWm i₀) b a δ
    (constant (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ ((Real.sqrt (δ:ℝ))⁻¹ • g))
  have hn : ‖constant (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ ((Real.sqrt (δ:ℝ))⁻¹ • g)‖ = ‖g‖ := by
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
      (normalized_norm_sq (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ hδ g)
  rw [hn] at hh
  exact hh

/-- Unit stochastic terminal energy persists under the actual small drift.
No endpoint lower bound or martingale-isometry conclusion is assumed. -/
theorem unit_lower (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
    (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
    (i₀ : ι) (a δ : ℝ≥0) (hδ : 0 < δ)
    (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (q : ι → E) (hq : ∑ i, ‖q i‖^2 = 1)
    (Y : Lp E 2 (spacetimeMeasure 𝓕 μ (a+δ))) (η : Lp E 2 μ)
    (hs : SectionIntegralSolution b hW hWm (a+δ) 0
      (-(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (TerminalSpikeNoise.noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ (a+δ) le_rfl q i)))
      (TerminalSpikeNoise.noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ (a+δ) le_rfl q) Y η) :
    1 ≤ ‖η‖+Real.sqrt ((a+δ:ℝ≥0):ℝ)*‖A.adjoint‖*‖Y‖+
      Real.sqrt (δ:ℝ)*‖∑ i, (C i).adjoint (q i)‖ := by
  let Z := TerminalSpikeNoise.noise (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ (a+δ) le_rfl q
  let f := -(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (Z i))
  let I := vectorLp b hW hWm (a+δ) (a+δ) Z
  have he : η = terminalDrift b (a+δ) f+I := endpoint_eq b hW hWm (a+δ) Y f Z η hs
  have hI : ‖I‖ = 1 := TerminalSpikeNoise.stochastic_norm b hWm i₀ hW hpair hchannels a δ (a+δ) le_rfl hδ q hq
  have hnorm : ‖I‖ ≤ ‖η‖+‖terminalDrift b (a+δ) f‖ := by
    have he' : I = η-terminalDrift b (a+δ) f := by rw [he]; abel
    rw [he']
    exact norm_sub_le _ _
  let L := VectorH2Extension.liftLinear (mΛ:=𝓕.predictable) b (BSDETerminal.terminal (μ:=μ) 𝓕 (a+δ)).toLinearMap
  have hlin : terminalDrift b (a+δ) f =
      -(terminalDrift b (a+δ) (A.adjoint.compLp Y)+terminalDrift b (a+δ) (∑ i, (C i).adjoint.compLp (Z i))) := by
    change L (-(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (Z i))) = -(L (A.adjoint.compLp Y)+L (∑ i, (C i).adjoint.compLp (Z i)))
    rw [map_neg,map_add]
  have hfirst := (TerminalDriftWindow.terminalDrift_norm b (a+δ) (A.adjoint.compLp Y)).trans
    (mul_le_mul_of_nonneg_left (A.adjoint.norm_compLp_le Y) (Real.sqrt_nonneg _))
  have hsecond := forcing_drift_bound (𝓕:=𝓕) (μ:=μ) b hWm i₀ a δ hδ C q
  have htotal : ‖terminalDrift b (a+δ) f‖ ≤ Real.sqrt ((a+δ:ℝ≥0):ℝ)*‖A.adjoint‖*‖Y‖+
      Real.sqrt (δ:ℝ)*‖∑ i, (C i).adjoint (q i)‖ := by
    rw [hlin,norm_neg]
    exact (norm_add_le _ _).trans (add_le_add (by simpa only [mul_assoc] using hfirst) hsecond)
  rw [hI] at hnorm
  linarith
end LinearStochastic.TerminalSpikeEstimate
