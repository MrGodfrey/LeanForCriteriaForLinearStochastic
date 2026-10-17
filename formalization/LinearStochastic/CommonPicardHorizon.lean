module

public import LinearStochastic.CommonInitialPredictable

@[expose] public section

/-! An actual positive contraction horizon for every fixed finite collection
of matrix coefficients. Uniform entry-sum bounds remove any unproved continuity
assumption on the horizon-dependent space-time operator norms. -/
noncomputable section
namespace LinearStochastic.CommonPicardHorizon
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open CommonVectorPicard
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {κ ν ι : Type*} [Fintype κ] [Fintype ν] [Fintype ι]

def matrixSize (A : Matrix κ ν ℝ) : ℝ := ∑ a, ∑ b, |A a b|

theorem matrixSize_nonneg (A : Matrix κ ν ℝ) : 0 ≤ matrixSize A := by
  unfold matrixSize
  positivity

omit [IsProbabilityMeasure μ] in
/-- A uniform bound by literal absolute matrix entries, valid on each horizon. -/
theorem matrixAction_norm_le (T : ℝ≥0) (A : Matrix κ ν ℝ) :
    ‖matrixAction (𝓕:=𝓕) (μ:=μ) T A‖ ≤ matrixSize A := by
  classical
  apply ContinuousLinearMap.opNorm_le_bound _ (matrixSize_nonneg A)
  intro X
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (matrixSize_nonneg A) (norm_nonneg X))).mpr
  intro a
  rw [matrixAction_apply]
  calc
    _ ≤ ∑ b, ‖A a b • X b‖ := norm_sum_le _ _
    _ = ∑ b, |A a b| * ‖X b‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ∑ b, |A a b| * ‖X‖ := Finset.sum_le_sum fun b _ ↦
      mul_le_mul_of_nonneg_left (norm_le_pi_norm X b) (abs_nonneg _)
    _ = (∑ b, |A a b|) * ‖X‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ matrixSize A * ‖X‖ := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg fun b _ ↦ abs_nonneg (A i b)) (Finset.mem_univ a))
      (norm_nonneg X)

omit [IsProbabilityMeasure μ] in
theorem rate_le (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) :
    rate (𝓕:=𝓕) (μ:=μ) T A C ≤
      (T : ℝ) * matrixSize A + Real.sqrt (T : ℝ) * ∑ i, matrixSize (C i) := by
  unfold rate
  exact add_le_add
    (mul_le_mul_of_nonneg_left (matrixAction_norm_le T A) T.coe_nonneg)
    (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ ↦ matrixAction_norm_le T (C i)) (Real.sqrt_nonneg _))

omit [IsProbabilityMeasure μ] in
/-- The short-time hypothesis is satisfiable for every actual finite matrix
system; the horizon is explicitly the square of 1/(4(K+1)). -/
theorem exists_positive_contraction_horizon (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) :
    ∃ T : ℝ≥0, 0 < T ∧ rate (𝓕:=𝓕) (μ:=μ) T A C < 1 := by
  let a := matrixSize A
  let c := ∑ i, matrixSize (C i)
  have ha : 0 ≤ a := matrixSize_nonneg A
  have hc : 0 ≤ c := Finset.sum_nonneg fun i _ ↦ matrixSize_nonneg (C i)
  let h : ℝ := 1 / (4 * (a+c+1))
  have hpos : 0 < h := by dsimp [h]; positivity
  have hle : h ≤ 1 := by
    dsimp [h]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hmul : h * (a+c+1) = 1/4 := by
    dsimp [h]
    field_simp
  let T : ℝ≥0 := ⟨h^2,sq_nonneg h⟩
  refine ⟨T, by change 0 < h^2; positivity, ?_⟩
  have hroot : Real.sqrt (T : ℝ) = h := by exact Real.sqrt_sq hpos.le
  have hT : (T : ℝ) ≤ h := by change h^2 ≤ h; nlinarith
  have hb := rate_le (𝓕:=𝓕) (μ:=μ) T A C
  rw [hroot] at hb
  change rate (𝓕:=𝓕) (μ:=μ) T A C ≤ (T : ℝ)*a + h*c at hb
  have hd := mul_le_mul_of_nonneg_right hT ha
  nlinarith

end LinearStochastic.CommonPicardHorizon
