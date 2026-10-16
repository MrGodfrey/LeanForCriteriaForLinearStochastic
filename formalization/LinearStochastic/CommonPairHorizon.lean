import LinearStochastic.CommonPicardHorizon

/-! A common genuinely positive Picard horizon for two actual coefficient
families, even when their state dimensions differ. -/
noncomputable section
namespace LinearStochastic.CommonPairHorizon
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open CommonVectorPicard CommonPicardHorizon
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {κ ν ι : Type*} [Fintype κ] [Fintype ν] [Fintype ι]

/-- The coefficient bounds, rather than norms on different horizon spaces,
provide a common positive contraction time. -/
theorem exists_common_contraction_horizon (A₁ : Matrix κ κ ℝ) (C₁ : ι → Matrix κ κ ℝ)
    (A₂ : Matrix ν ν ℝ) (C₂ : ι → Matrix ν ν ℝ) :
    ∃ T : ℝ≥0, 0 < T ∧ rate (𝓕:=𝓕) (μ:=μ) T A₁ C₁ < 1 ∧
      rate (𝓕:=𝓕) (μ:=μ) T A₂ C₂ < 1 := by
  let a₁ := matrixSize A₁
  let c₁ := ∑ i, matrixSize (C₁ i)
  let a₂ := matrixSize A₂
  let c₂ := ∑ i, matrixSize (C₂ i)
  have ha₁ : 0 ≤ a₁ := matrixSize_nonneg A₁
  have hc₁ : 0 ≤ c₁ := Finset.sum_nonneg fun i _ ↦ matrixSize_nonneg (C₁ i)
  have ha₂ : 0 ≤ a₂ := matrixSize_nonneg A₂
  have hc₂ : 0 ≤ c₂ := Finset.sum_nonneg fun i _ ↦ matrixSize_nonneg (C₂ i)
  let K := a₁+c₁+a₂+c₂
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let h : ℝ := 1 / (4 * (K+1))
  have hpos : 0 < h := by dsimp [h]; positivity
  have hle : h ≤ 1 := by
    dsimp [h]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hmul : h * (K+1) = 1/4 := by dsimp [h]; field_simp
  let T : ℝ≥0 := ⟨h^2,sq_nonneg h⟩
  have hroot : Real.sqrt (T : ℝ) = h := Real.sqrt_sq hpos.le
  have hT : (T : ℝ) ≤ h := by change h^2 ≤ h; nlinarith
  have hbound (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a+c ≤ K) :
      (T : ℝ)*a+h*c < 1 := by
    have h₁ := mul_le_mul_of_nonneg_right hT ha
    have h₂ := mul_le_mul_of_nonneg_left hac hpos.le
    nlinarith
  refine ⟨T, by change 0 < h^2; positivity, ?_, ?_⟩
  · have hb := rate_le (𝓕:=𝓕) (μ:=μ) T A₁ C₁
    rw [hroot] at hb
    exact hb.trans_lt (hbound a₁ c₁ ha₁ hc₁ (by dsimp [K]; linarith))
  · have hb := rate_le (𝓕:=𝓕) (μ:=μ) T A₂ C₂
    rw [hroot] at hb
    exact hb.trans_lt (hbound a₂ c₂ ha₂ hc₂ (by dsimp [K]; linarith))

end LinearStochastic.CommonPairHorizon
