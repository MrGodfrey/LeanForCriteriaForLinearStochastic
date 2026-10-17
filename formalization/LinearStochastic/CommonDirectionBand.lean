module

public import LinearStochastic.CommonDoleansBand
public import LinearStochastic.CommonDirectionIntegral
public import LinearStochastic.CommonItoLocality

@[expose] public section

noncomputable section
namespace LinearStochastic.CommonDirectionBand
open MeasureTheory ProbabilityTheory CommonItoCLM CommonItoMultichannel
open scoped NNReal BigOperators
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ι → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  [CommonItoIsometry.ForwardIndependent B 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hB : IsPreBrownianReal B μ) (hBm : ∀ t, Measurable (B t))
  (c : ι → ℝ) (hlinear : ∀ t ω, B t ω = ∑ i, c i * W i t ω)

include hlinear hB hBm in
/-- A true Brownian direction's exponential band has an actual multichannel
integrand with the same band support. -/
theorem band_mem_range (hBc : ∀ ω, Continuous fun t => B t ω)
    (a b T : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T) (σ : ℝ) :
    ∃ φ : ι → Lp ℝ 2 (spacetimeMeasure 𝓕 μ T),
      (∀ i, ∀ᵐ p ∂spacetimeMeasure 𝓕 μ T, p.1 ≤ a → φ i p = 0) ∧
      (∀ i, ∀ᵐ p ∂spacetimeMeasure 𝓕 μ T, b < p.1 → φ i p = 0) ∧
      (fun ω => Real.exp (σ * B b ω - σ ^ 2 * (b : ℝ) / 2) -
        Real.exp (σ * B a ω - σ ^ 2 * (a : ℝ) / 2)) =ᵐ[μ]
          sumIntegral hW hWm T φ := by
  obtain ⟨φ,ha,hb,he⟩ := CommonDoleansBand.band_mem_range (𝓕 := 𝓕) hB hBm hBc a b T hab hbT σ
  refine ⟨fun i => c i • φ, ?_, ?_, ?_⟩
  · intro i
    filter_upwards [Lp.coeFn_smul (c i) φ,ha] with p hs hp hpa
    exact hs.trans (by change c i * φ p = 0; rw [hp hpa,mul_zero])
  · intro i
    filter_upwards [Lp.coeFn_smul (c i) φ,hb] with p hs hp hpb
    exact hs.trans (by change c i * φ p = 0; rw [hp hpb,mul_zero])
  · have hi : sumIntegral hW hWm T (fun i => c i • φ) =
        itoIntegralCLM_T (𝓕 := 𝓕) hB T hBm φ := by
      change (∑ i, (itoIntegralCLM_T (𝓕 := 𝓕) (hW i) T (hWm i)) (c i • φ)) = _
      calc
        _ = ∑ i, c i • itoIntegralCLM_T (𝓕 := 𝓕) (hW i) T (hWm i) φ := by
          apply Finset.sum_congr rfl
          intro i _
          exact (itoIntegralCLM_T (𝓕 := 𝓕) (hW i) T (hWm i)).map_smul (c i) φ
        _ = _ := (CommonDirectionIntegral.integral_direction hW hWm hB hBm c hlinear T φ).symm
    change _ =ᵐ[μ] (sumIntegral hW hWm T _)
    rw [hi]
    exact he

include hlinear hB hBm in
/-- A past-measurable factor times a true direction exponential band has a
genuine multichannel integrand whenever the actual sample-side product is L². -/
theorem factored_band_mem_range (hBc : ∀ ω, Continuous fun t => B t ω)
    (a b T : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T) (σ : ℝ)
    (Z : Ω → ℝ) (hZm : Measurable[𝓕 a] Z)
    (hZ : MemLp (fun ω => Z ω * (Real.exp (σ * B b ω - σ ^ 2 * (b : ℝ) / 2) -
      Real.exp (σ * B a ω - σ ^ 2 * (a : ℝ) / 2))) 2 μ) :
    ∃ φ : ι → Lp ℝ 2 (spacetimeMeasure 𝓕 μ T),
      (∀ i, ∀ᵐ p ∂spacetimeMeasure 𝓕 μ T, p.1 ≤ a → φ i p = 0) ∧
      (∀ i, ∀ᵐ p ∂spacetimeMeasure 𝓕 μ T, b < p.1 → φ i p = 0) ∧
      (fun ω => Z ω * (Real.exp (σ * B b ω - σ ^ 2 * (b : ℝ) / 2) -
        Real.exp (σ * B a ω - σ ^ 2 * (a : ℝ) / 2))) =ᵐ[μ]
          sumIntegral hW hWm T φ := by
  obtain ⟨φ,ha,hb,he⟩ := CommonDoleansBand.band_mem_range (𝓕 := 𝓕) hB hBm hBc a b T hab hbT σ
  have hZI : MemLp (fun ω => Z ω * itoIntegralCLM_T (𝓕 := 𝓕) hB T hBm φ ω) 2 μ := by
    apply (memLp_congr_ae (he.mono (fun ω hω => congrArg (fun x => Z ω * x) hω))).mp hZ
  obtain ⟨ψ,hψ,hI⟩ := CommonItoLocality.itoIntegralCLM_T_smul_of_memLp
    (𝓕 := 𝓕) hB T a hBm Z hZm φ ha hZI
  have hψa : ∀ᵐ p ∂trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBm, p.1 ≤ a → ψ p = 0 := by
    filter_upwards [hψ,ha] with p hp ha hpa
    exact hp.trans (by rw [ha hpa,mul_zero])
  have hψb : ∀ᵐ p ∂trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBm, b < p.1 → ψ p = 0 := by
    filter_upwards [hψ,hb] with p hp hb hpb
    exact hp.trans (by rw [hb hpb,mul_zero])
  refine ⟨fun i => c i • ψ, ?_, ?_, ?_⟩
  · intro i
    filter_upwards [Lp.coeFn_smul (c i) ψ,hψa] with p hs hp hpa
    exact hs.trans (by change c i * ψ p = 0; rw [hp hpa,mul_zero])
  · intro i
    filter_upwards [Lp.coeFn_smul (c i) ψ,hψb] with p hs hp hpb
    exact hs.trans (by change c i * ψ p = 0; rw [hp hpb,mul_zero])
  · have hi : sumIntegral hW hWm T (fun i => c i • ψ) =
        itoIntegralCLM_T (𝓕 := 𝓕) hB T hBm ψ := by
      change (∑ i, (itoIntegralCLM_T (𝓕 := 𝓕) (hW i) T (hWm i)) (c i • ψ)) = _
      calc
        _ = ∑ i, c i • itoIntegralCLM_T (𝓕 := 𝓕) (hW i) T (hWm i) ψ := by
          apply Finset.sum_congr rfl
          intro i _
          exact (itoIntegralCLM_T (𝓕 := 𝓕) (hW i) T (hWm i)).map_smul (c i) ψ
        _ = _ := (CommonDirectionIntegral.integral_direction hW hWm hB hBm c hlinear T ψ).symm
    change _ =ᵐ[μ] (sumIntegral hW hWm T _)
    rw [hi]
    exact Filter.EventuallyEq.trans (he.mono (fun ω hω => congrArg (fun x => Z ω * x) hω)) hI.symm

end LinearStochastic.CommonDirectionBand
