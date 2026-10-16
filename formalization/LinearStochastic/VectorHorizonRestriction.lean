import LinearStochastic.CommonHorizonRestriction
import LinearStochastic.VectorItoNaturality

/-! Genuine horizon restriction of vector predictable L² classes and their
constructed vector Itô integrals, on the same sample space and filtration. -/
noncomputable section
namespace LinearStochastic.VectorHorizonRestriction
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct VectorItoNaturality

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

theorem measure_le {t T : ℝ≥0} (h : t ≤ T) :
    spacetimeMeasure 𝓕 μ t ≤ spacetimeMeasure 𝓕 μ T := by
  apply Measure.le_iff.mpr
  intro s hs
  simp only [spacetimeMeasure,trim_measurableSet_eq _ hs]
  exact Measure.prod_mono (Measure.restrict_mono (Ioc_subset_Ioc_right h) le_rfl) le_rfl s

variable {E : Type*} [NormedAddCommGroup E]

def restrict {t T : ℝ≥0} (h : t ≤ T) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    Lp E 2 (spacetimeMeasure 𝓕 μ t) := ((Lp.memLp f).mono_measure (measure_le h)).toLp f

theorem restrict_ae {t T : ℝ≥0} (h : t ≤ T) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    restrict h f =ᵐ[spacetimeMeasure 𝓕 μ t] f := MemLp.coeFn_toLp _

theorem restrict_comp [NormedSpace ℝ E] {t T : ℝ≥0} (h : t ≤ T) (L : E →L[ℝ] E)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    restrict h (L.compLp f) = L.compLp (restrict h f) := by
  apply Lp.ext
  filter_upwards [restrict_ae h (L.compLp f),restrict_ae h f,
    (L.coeFn_compLp f).filter_mono (ae_mono (measure_le h)),L.coeFn_compLp (restrict h f)]
    with z hr hf hL hLr
  rw [hr,hL,hLr,hf]

section Ito
variable [InnerProductSpace ℝ E] {κ ι : Type*} [Fintype κ] [Fintype ι]
  (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

omit [Fintype ι] in
theorem coordinate_restrict {t T : ℝ≥0} (h : t ≤ T) (a : κ) (i : ι)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    coordinate b a (restrict h f) =
      CommonHorizonRestriction.restriction (hWm i) h (coordinate b a f) := by
  apply Lp.ext
  filter_upwards [coordinate_ae b a (restrict h f),restrict_ae h f,
    CommonHorizonRestriction.restriction_ae (hWm i) h (coordinate b a f),
    (coordinate_ae b a f).filter_mono (ae_mono (measure_le h))] with z hc hr hs hf
  exact (hc.trans (congrArg (fun x => inner ℝ (b a) x) hr)).trans (hs.trans hf).symm

/-- The vector Itô L² class at a fixed time is independent of the later
integrand horizon, proved by actual scalar restriction and finite coordinates. -/
theorem vectorLp_restrict {s t T : ℝ≥0} (hs : s ≤ t) (h : t ≤ T)
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    vectorLp b hW hWm t s (fun i => restrict h (φ i)) = vectorLp b hW hWm T s φ := by
  rw [vectorLp_coordinates,vectorLp_coordinates]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact (congrArg (CommonItoProcessGeneral.itoProcessCLM (hW i) t s (hWm i))
    (coordinate_restrict b hWm h a i (φ i))).trans
    (CommonHorizonRestriction.process_restriction (hW i) (hWm i) hs h _)

theorem vectorProcess_restrict {s t T : ℝ≥0} (hs : s ≤ t) (h : t ≤ T)
    (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    vectorProcess b hW hWm t (fun i => restrict h (φ i)) s =ᵐ[μ]
      vectorProcess b hW hWm T φ s := by
  have he := vectorProcess_ae_vectorLp b hW hWm t s (fun i => restrict h (φ i))
  rw [vectorLp_restrict b hW hWm hs h] at he
  exact he.trans (vectorProcess_ae_vectorLp b hW hWm T s φ).symm
end Ito

end LinearStochastic.VectorHorizonRestriction
