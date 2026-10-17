module

public import LinearStochastic.CommonNaturalIntegral
public import LinearStochastic.CommonIntegrandSupport
public import MathFin.Foundations.DoleansStepRepresentation

@[expose] public section

noncomputable section
namespace LinearStochastic.CommonDoleansBand
open MeasureTheory ProbabilityTheory CommonItoCLM
open scoped NNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [hF : CommonItoIsometry.ForwardIndependent B 𝓕 μ]
  (hB : IsPreBrownianReal B μ) (hBm : ∀ t, Measurable (B t))

include hF in
omit [IsProbabilityMeasure μ] in
/-- The actual scalar natural filtration is contained in any given filtration
for which the same process is strongly adapted. -/
theorem natural_le : MathFin.ItoIntegralL2.natFiltration hBm ≤ 𝓕 := by
  intro t
  refine iSup_le fun s => iSup_le fun hs => ?_
  exact ((hF.adapted s).measurable.mono (𝓕.mono hs) le_rfl).comap_le

/-- The actual Doléans exponential band formula in an admissible common
filtration. It is transported from the proved scalar formula via the proved
canonical integrand inclusion and integral equality. -/
theorem band_mem_range (hBc : ∀ ω, Continuous fun t => B t ω)
    (a b T : ℝ≥0) (hab : a ≤ b) (hbT : b ≤ T) (σ : ℝ) :
    ∃ φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBm),
      (∀ᵐ p ∂trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBm, p.1 ≤ a → φ p = 0) ∧
      (∀ᵐ p ∂trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBm, b < p.1 → φ p = 0) ∧
      (fun ω => Real.exp (σ * B b ω - σ ^ 2 * (b : ℝ) / 2) -
        Real.exp (σ * B a ω - σ ^ 2 * (a : ℝ) / 2)) =ᵐ[μ]
          itoIntegralCLM_T (𝓕 := 𝓕) hB T hBm φ := by
  letI : CommonItoIsometry.ForwardIndependent B (MathFin.ItoIntegralL2.natFiltration hBm) μ :=
    CommonNaturalIntegral.naturalForward hB hBm
  obtain ⟨φ,ha,hb,he⟩ := MathFin.constDoleans_band_mem_range hB hBm hBc a b T hab hbT σ
  let h := natural_le (μ := μ) (𝓕 := 𝓕) hBm
  refine ⟨CommonFiltrationTransport.integrandInclusion h T φ,
    CommonIntegrandSupport.inclusion_vanishes_before h T a φ ha,
    CommonIntegrandSupport.inclusion_vanishes_after h T b φ hb, ?_⟩
  have hi := CommonFiltrationTransport.integral_inclusion hB hBm h T φ
  rw [CommonNaturalIntegral.common_eq_natural hB hBm T] at hi
  rw [hi]
  exact he

end LinearStochastic.CommonDoleansBand
