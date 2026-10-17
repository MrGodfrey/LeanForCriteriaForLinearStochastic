module

public import LinearStochastic.CommonSmallTimeBound
public import LinearStochastic.HilbertEndpointBound

@[expose] public section

/-! Actual additive-noise vector SDE state estimates on shrinking horizons.
All constants are computed from the original orthonormal matrix coefficients. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.HilbertSmallTimeBound
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel SectionLinearDuality HilbertLocalSolution HilbertBrownianRealization
open LpOrthonormalCoordinates VectorItoProduct
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

include c hWc in
/-- No stochastic state bound is assumed: the actual section solution is
converted to the genuine coordinate solution and its Picard bound is applied. -/
theorem additive_bound (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (η : Ω → E)
    (hY : SectionIntegralSolution b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T 0
      (A.compLp Y+B.compLp u) (fun i ↦ (D i).compLp u) Y η)
    (hT : (T:ℝ)*CommonPicardHorizon.matrixSize (coefficientMatrix b b A) < 1) :
    ‖Y‖ ≤ (Fintype.card κ : ℝ)*CommonSmallTimeBound.additiveFactor T
      (coefficientMatrix b b A) (coefficientMatrix b c B)
      (fun i ↦ coefficientMatrix b c (D i))*‖u‖ := by
  have hY' : SectionIntegralSolution b (fun i ↦ (hW i).toIsPreBrownianReal) hWm T 0
      (A.compLp Y+B.compLp u) (fun i ↦ (0 : E →L[ℝ] E).compLp Y+(D i).compLp u) Y η := by
    have hz : (0 : E →L[ℝ] E).compLp Y = 0 := by
      apply Lp.ext
      filter_upwards [(0 : E →L[ℝ] E).coeFn_compLp Y,Lp.coeFn_zero E 2 (spacetimeMeasure 𝓕 μ T)] with z h1 h2
      simpa only [zero_apply,Pi.zero_apply] using h1.trans h2.symm
    simpa only [hz,zero_add] using hY
  let q := coordinateSolution b c hW hWm i₀ T A B (fun _ ↦ 0) D
    (0 : Ω → E) stronglyMeasurable_zero MemLp.zero u Y η hY'
  have hc : (fun i : ι ↦ coefficientMatrix b b (0 : E →L[ℝ] E)) = 0 := by
    funext i j k
    simp only [coefficientMatrix,zero_apply,inner_zero_right,Pi.zero_apply,Matrix.zero_apply]
  have hξ : (fun j ω ↦ inner ℝ (b j) ((0 : Ω → E) ω)) = 0 := by
    funext j ω
    simp only [Pi.zero_apply,inner_zero_right]
  let q₀ := CommonSolutionFixedPoint.withInitial (fun i ↦ (hW i).toIsPreBrownianReal) hWm T
    (coefficientMatrix b b A) (coefficientMatrix b c B) (fun i : ι ↦ coefficientMatrix b b (0 : E →L[ℝ] E))
    (fun i ↦ coefficientMatrix b c (D i)) (fun j ω ↦ inner ℝ (b j) ((0 : Ω → E) ω)) 0
    (fun j ↦ coordinate c j u) q (fun j ↦ Filter.Eventually.of_forall (fun ω ↦ by simp))
  have hbound : CommonUniformHorizon.bound T (coefficientMatrix b b A)
      (fun i : ι ↦ coefficientMatrix b b (0 : E →L[ℝ] E)) =
      (T:ℝ)*CommonPicardHorizon.matrixSize (coefficientMatrix b b A) := by
    rw [hc]
    simp [CommonUniformHorizon.bound,CommonPicardHorizon.matrixSize]
  have hh := CommonSmallTimeBound.state_bound (fun i ↦ (hW i).toIsPreBrownianReal)
    hWm hWc i₀ T (coefficientMatrix b b A) (coefficientMatrix b c B)
    (fun i : ι ↦ coefficientMatrix b b (0 : E →L[ℝ] E))
    (fun i ↦ coefficientMatrix b c (D i)) (fun j ↦ coordinate c j u) q₀ (by rw [hbound]; exact hT)
  have hstate : q₀.X = fun j ↦ coordinate b j Y := rfl
  rw [hstate,hbound] at hh
  have hh0 : ‖fun j ↦ coordinate b j Y‖ ≤ CommonSmallTimeBound.additiveFactor T
      (coefficientMatrix b b A) (coefficientMatrix b c B) (fun i ↦ coefficientMatrix b c (D i)) *
      ‖fun j ↦ coordinate c j u‖ := by simpa only [CommonSmallTimeBound.additiveFactor,div_mul_eq_mul_div] using hh
  have hfactor : 0 ≤ CommonSmallTimeBound.additiveFactor T (coefficientMatrix b b A)
      (coefficientMatrix b c B) (fun i ↦ coefficientMatrix b c (D i)) := by
    apply div_nonneg
    · exact CommonForwardBounds.inputBound_nonneg T _ _
    · exact (sub_pos.mpr hT).le
  have hh' := hh0.trans (mul_le_mul_of_nonneg_left
    (HilbertEndpointBound.coordinates_norm_le (mΛ:=𝓕.predictable) c u) hfactor)
  exact (HilbertEndpointBound.norm_le_card_coordinates (mΛ:=𝓕.predictable) b Y).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh' (Nat.cast_nonneg (Fintype.card κ)))
end LinearStochastic.HilbertSmallTimeBound
