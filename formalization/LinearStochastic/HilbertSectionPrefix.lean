import LinearStochastic.VectorH2Series
import LinearStochastic.SectionHorizonRestriction

/-! A genuine controlled Hilbert integral solution restricts to its actual
prefix with the same coefficient maps and the truly restricted control. -/
set_option maxHeartbeats 1000000
noncomputable section
namespace LinearStochastic.HilbertSectionPrefix
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace
open CommonItoMultichannel VectorHorizonRestriction LinearDuality SectionLinearDuality
variable {Ω E U : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U] {𝓕 : Filtration ℝ≥0 mΩ}

theorem restrict_compLp {t T : ℝ≥0} (h : t ≤ T) (L : U →L[ℝ] E)
    (f : Lp U 2 (spacetimeMeasure 𝓕 μ T)) :
    restrict h (L.compLp f) = L.compLp (restrict h f) := by
  apply Lp.ext
  filter_upwards [restrict_ae h (L.compLp f),restrict_ae h f,
    (L.coeFn_compLp f).filter_mono (ae_mono (measure_le h)),L.coeFn_compLp (restrict h f)]
    with z hr hf hL hLr
  rw [hr,hL,hLr,hf]


theorem restrict_add {t T : ℝ≥0} (h : t ≤ T) (f g : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    restrict h (f+g) = restrict h f+restrict h g := (VectorH2Series.restrictCLM h).map_add f g

variable {κ ι : Type*} [Fintype κ] [Fintype ι]
  (b : OrthonormalBasis κ ℝ E) {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

theorem controlled_prefix {t T : ℝ≥0} (h : t ≤ T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ξ XT Xt : Ω → E) (u : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ (A.compLp X+B.compLp u)
      (fun i => (C i).compLp X+(D i).compLp u) X XT)
    (hXt : Xt =ᵐ[μ] integralState b hW hWm T ξ (A.compLp X+B.compLp u)
      (fun i => (C i).compLp X+(D i).compLp u) (t:ℝ)) :
    SectionIntegralSolution b hW hWm t ξ (A.compLp (restrict h X)+B.compLp (restrict h u))
      (fun i => (C i).compLp (restrict h X)+(D i).compLp (restrict h u)) (restrict h X) Xt := by
  have hs := SectionHorizonRestriction.section_restrict b hW hWm h ξ XT Xt
    (A.compLp X+B.compLp u) X (fun i => (C i).compLp X+(D i).compLp u) hX hXt
  simpa only [restrict_add,restrict_compLp] using hs

end LinearStochastic.HilbertSectionPrefix
