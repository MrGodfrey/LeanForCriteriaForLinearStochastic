import LinearStochastic.CommonItoContinuousVersion
import LinearStochastic.ContinuousDoobL2

/-! Genuine continuous S² versions of the common-filtration stochastic integral. -/
noncomputable section
namespace LinearStochastic.CommonItoS2
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open CommonItoCLM CommonItoProcessGeneral CommonItoContinuousVersion ContinuousDoobL2

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [CommonItoIsometry.ForwardIndependent B 𝓕 μ] (hB : IsPreBrownianReal B μ)

/-- The true L² continuous extension admits an everywhere-continuous adapted
martingale version with the actual S² maximal norm bound. The filtration here
adds ambient-measurable null sets; right-continuity is neither assumed nor
asserted. This statement is on an arbitrary underlying probability space. -/
theorem exists_continuous_s2_modification (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    ∃ X : ℝ≥0 → Ω → ℝ,
      (∀ t, t ≤ T → X t =ᵐ[μ] itoProcessCLM hB T t hBmeas φ) ∧
      (∀ ω, Continuous fun t ↦ X t ω) ∧
      Martingale X (augFiltration (𝓕 := 𝓕) (μ := μ) hBmeas) μ ∧
      MemLp (pathSup X T) 2 μ ∧
      eLpNorm (pathSup X T) 2 μ ≤ 2 * ‖φ‖ₑ ∧
      Integrable (fun ω ↦ pathSup X T ω ^ 2) μ := by
  obtain ⟨X, hmod, hc, hm, _⟩ := exists_continuous_martingale_modification hB T hBmeas hBcont φ
  have hXT : MemLp (X T) 2 μ :=
    (memLp_congr_ae (hmod T le_rfl)).mpr (Lp.memLp (itoProcessCLM hB T T hBmeas φ))
  have hs := pathSup_memLp hm hc T hXT
  refine ⟨X, hmod, hc, hm, hs, ?_, hs.integrable_sq⟩
  have h := pathSup_eLpNorm_le hm hc T
  rw [eLpNorm_congr_ae (hmod T le_rfl), ← Lp.enorm_def,
    ← ofReal_norm, itoProcessCLM_norm_terminal hB T hBmeas φ, ofReal_norm] at h
  exact h

end LinearStochastic.CommonItoS2
