module

public import LinearStochastic.CommonItoProcessGeneral

@[expose] public section

noncomputable section
namespace LinearStochastic.CommonItoMartingaleVersion
open MeasureTheory ProbabilityTheory CommonItoCLM CommonItoProcessGeneral
open scoped NNReal ENNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [CommonItoIsometry.ForwardIndependent B 𝓕 μ]
  (hB : IsPreBrownianReal B μ)

/-- A specified strongly adapted version, using the actual conditional expectation
of the already constructed terminal Itô integral. -/
def integralProcess (T : ℝ≥0) (hBm : ∀ t, Measurable (B t))
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm)) (t : ℝ≥0) : Ω → ℝ :=
  μ[(itoIntegralCLM_T (𝓕:=𝓕) hB T hBm f : Ω → ℝ) | 𝓕 t]

theorem integralProcess_martingale (T : ℝ≥0) (hBm : ∀ t, Measurable (B t))
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm)) :
    Martingale (integralProcess hB T hBm f) 𝓕 μ := by
  refine ⟨fun t ↦ stronglyMeasurable_condExp, ?_⟩
  intro i j hij
  exact condExp_condExp_of_le (𝓕.mono hij) (𝓕.le j)

/-- This is a version of the genuine continuous-extension integral at each time.
No common null set or pathwise continuity is asserted here. -/
theorem integralProcess_ae_eq (T t : ℝ≥0) (hBm : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm)) :
    integralProcess hB T hBm f t =ᵐ[μ] (itoProcessCLM hB T t hBm f : Ω → ℝ) := by
  rw [itoProcessCLM_eq_condExpL2]
  have hh := (Lp.memLp (itoIntegralCLM_T (𝓕:=𝓕) hB T hBm f)).condExpL2_ae_eq_condExp
    (𝕜:=ℝ) (𝓕.le t)
  rw [Lp.toLp_coeFn] at hh
  exact hh.symm

theorem integralProcess_memLp (T t : ℝ≥0) (hBm : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm)) :
    MemLp (integralProcess hB T hBm f t) 2 μ :=
  (memLp_congr_ae (integralProcess_ae_eq hB T t hBm f)).mpr (Lp.memLp (itoProcessCLM hB T t hBm f))

theorem integralProcess_toLp (T t : ℝ≥0) (hBm : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm)) :
    (integralProcess_memLp hB T t hBm f).toLp _ = itoProcessCLM hB T t hBm f := by
  apply Lp.ext
  exact (integralProcess_memLp hB T t hBm f).coeFn_toLp.trans (integralProcess_ae_eq hB T t hBm f)

theorem integralProcess_terminal_ae (T : ℝ≥0) (hBm : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm)) :
    integralProcess hB T hBm f T =ᵐ[μ] (itoIntegralCLM_T (𝓕:=𝓕) hB T hBm f : Ω → ℝ) := by
  simpa only [itoProcessCLM_terminal_eq] using integralProcess_ae_eq hB T T hBm f

theorem integralProcess_zero_ae (T : ℝ≥0) (hBm : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm)) :
    integralProcess hB T hBm f 0 =ᵐ[μ] 0 := by
  have h := integralProcess_ae_eq hB T 0 hBm f
  rw [itoProcessCLM_zero_time] at h
  exact h.trans (Lp.coeFn_zero ℝ 2 μ)

theorem integralProcess_l2_continuous (T : ℝ≥0) (hBm : ∀ u, Measurable (B u))
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm)) :
    Continuous (fun t ↦ (integralProcess_memLp hB T t hBm f).toLp _) := by
  simp_rw [integralProcess_toLp]
  exact itoIntegralProcessGen_l2_continuous hB T hBm f

end LinearStochastic.CommonItoMartingaleVersion
