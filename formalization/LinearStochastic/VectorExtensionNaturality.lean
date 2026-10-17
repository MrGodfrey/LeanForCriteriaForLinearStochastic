module

public import LinearStochastic.VectorH2Extension
public import LinearStochastic.PredictableConstant

@[expose] public section

/-! True coefficient naturality for the constructed window extension. -/
noncomputable section
namespace LinearStochastic.VectorExtensionNaturality
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct
variable {Ω E F κ τ : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Fintype κ] [Fintype τ] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ F)
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent W 𝓕 μ] (hWm : ∀ t, Measurable (W t))

/-- Coefficient maps commute with the actual zero extension, proved from the
ambient product-measure representatives, without any integral oracle. -/
theorem compLp (a δ T : ℝ≥0) (h : a+δ ≤ T) (L : E →L[ℝ] F)
    (f : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ)) :
    L.compLp (VectorH2Extension.extendShift b hWm a δ T h f) =
      VectorH2Extension.extendShift c hWm a δ T h (L.compLp f) := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable 𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
  have hw := VectorH2Extension.window_ae (μ:=μ) a δ T h
    (fun z ↦ L.compLp f z = L (f z))
    (ae_of_ae_trim (CommonTimeShift.filtration 𝓕 a).predictable_le_prod (L.coeFn_compLp f))
  filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod
    (L.coeFn_compLp (VectorH2Extension.extendShift b hWm a δ T h f)),
    VectorH2Extension.extendShift_ae b hWm a δ T h f,
    VectorH2Extension.extendShift_ae c hWm a δ T h (L.compLp f),hw] with z hL hf hLf hw
  rw [hL,hf,hLf]
  by_cases hz : a < z.1 ∧ z.1 ≤ a+δ
  · simp only [if_pos hz]
    exact (hw hz).symm
  · simp only [if_neg hz,map_zero]

/-- In particular, an actual normalized constant window is transformed by its
literal coefficient, including singular and zero coefficient maps. -/
theorem normalized_constant (a δ T : ℝ≥0) (h : a+δ ≤ T) (L : E →L[ℝ] F) (v : E) :
    L.compLp (VectorH2Extension.extendShift b hWm a δ T h
      (PredictableConstant.constant (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ ((Real.sqrt (δ:ℝ))⁻¹ • v))) =
    VectorH2Extension.extendShift c hWm a δ T h
      (PredictableConstant.constant (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ ((Real.sqrt (δ:ℝ))⁻¹ • L v)) := by
  rw [compLp b c hWm,PredictableConstant.constant_compLp,map_smul]
end LinearStochastic.VectorExtensionNaturality
