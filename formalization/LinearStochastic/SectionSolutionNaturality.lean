import LinearStochastic.SectionLinearDuality
import LinearStochastic.VectorItoNaturality

/-! The actual Lebesgue and Itô decomposition is preserved by a state-space
linear map. The proof uses only fixed-time equalities of the raw Itô version. -/
noncomputable section
namespace LinearStochastic.SectionSolutionNaturality
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct LinearDuality SectionLinearDuality

section Drift
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {𝓕 : Filtration ℝ≥0 mΩ}

omit [CompleteSpace E] in
/-- Composition of the predictable L² class agrees with its actual real-clock
pointwise composition on the genuine product measure. -/
theorem real_compLp_ae (T : ℝ≥0) (L : E →L[ℝ] E)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    (fun z : ℝ × Ω => L.compLp f (z.1.toNNReal,z.2)) =ᵐ[
      (volume.restrict (Ioc 0 (T : ℝ))).prod μ]
      fun z => L (f (z.1.toNNReal,z.2)) := by
  have h := ae_eq_of_ae_eq_trim (hm := 𝓕.predictable_le_prod) (L.coeFn_compLp f)
  exact ((RealTimeBridge.toNNReal_measurePreserving T).prod
    (MeasurePreserving.id μ)).quasiMeasurePreserving.ae_eq_comp h

/-- Linear maps commute with the actual pathwise drift integral at each time
within the horizon. Path integrability and common integral null sets follow
from actual predictable L² integrability and Fubini. -/
theorem primitive_comp_ae (T : ℝ≥0) (s : ℝ) (hs : s ≤ T) (L : E →L[ℝ] E)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    (fun ω => ∫ t in Ioc 0 s, L.compLp f (t.toNNReal,ω)) =ᵐ[μ]
      fun ω => L (∫ t in Ioc 0 s, f (t.toNNReal,ω)) := by
  have he := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae (real_compLp_ae T L f))
  have hi := ((RealTimeBridge.predictable_memLp_real_extension T μ 𝓕 f).integrable one_le_two).prod_left_ae
  filter_upwards [he,hi] with ω he hi
  have hsub : Ioc (0 : ℝ) s ⊆ Ioc 0 (T : ℝ) := Ioc_subset_Ioc_right hs
  have hes : (fun t => L.compLp f (t.toNNReal,ω)) =ᵐ[volume.restrict (Ioc 0 s)]
      fun t => L (f (t.toNNReal,ω)) :=
    (ae_restrict_of_ae_restrict_of_subset hsub he)
  rw [integral_congr_ae hes]
  exact L.integral_comp_comm (IntegrableOn.mono_set hi hsub)
end Drift

section Processes
variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

theorem integralState_comp_ae (T : ℝ≥0) (s : ℝ) (hs : s ≤ T)
    (L : E →L[ℝ] E) (ξ : Ω → E) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    integralState b hW hWm T (fun ω => L (ξ ω)) (L.compLp f)
      (fun i => L.compLp (φ i)) s =ᵐ[μ]
      fun ω => L (integralState b hW hWm T ξ f φ s ω) := by
  filter_upwards [primitive_comp_ae T s hs L f,
    VectorItoNaturality.vectorProcess_comp_ae b hW hWm T s.toNNReal L φ] with ω hd hi
  simp only [integralState,hd,hi,map_add]

/-- A genuine linear-image integral solution, with every coefficient and both
endpoint values mapped. No new solution or naturality property is assumed. -/
theorem SectionIntegralSolution.map (T : ℝ≥0) (L : E →L[ℝ] E) (ξ : Ω → E)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT : Ω → E)
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT) :
    SectionIntegralSolution b hW hWm T (fun ω => L (ξ ω)) (L.compLp f)
      (fun i => L.compLp (φ i)) (L.compLp X) (fun ω => L (XT ω)) := by
  constructor
  · filter_upwards [hX.sections,Measure.ae_ae_of_ae_prod (real_compLp_ae T L X),
      ae_restrict_mem measurableSet_Ioc] with s hs hL hsm
    filter_upwards [hs,hL,integralState_comp_ae b hW hWm T s hsm.2 L ξ f φ]
      with ω hs hL hstate
    rw [hL,hs,hstate]
  · filter_upwards [hX.terminal,integralState_comp_ae b hW hWm T T le_rfl L ξ f φ]
      with ω hx hstate
    rw [hstate,hx]
end Processes

#print axioms SectionIntegralSolution.map
end LinearStochastic.SectionSolutionNaturality
