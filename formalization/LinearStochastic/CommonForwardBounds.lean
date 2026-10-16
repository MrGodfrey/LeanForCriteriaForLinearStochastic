import LinearStochastic.CommonSolutionFixedPoint
import LinearStochastic.CommonUniformHorizon
import LinearStochastic.BSDEProcessLift

/-! Genuine quantitative dependence of the controlled forward Picard solution
on its initial random variable and control. All constants use literal matrix
entries and are independent of the filtration and restart location. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonForwardBounds
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open CommonVectorPicard CommonPicardHorizon CommonInitialPredictable CommonSolutionData
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

/-- An explicit matrix-entry bound for the control contribution. -/
def inputBound (T : ℝ≥0) (B : Matrix κ ν ℝ) (D : ι → Matrix κ ν ℝ) : ℝ :=
  (T:ℝ)*matrixSize B + Real.sqrt (T:ℝ)*∑ i, matrixSize (D i)

theorem inputBound_nonneg (T : ℝ≥0) (B : Matrix κ ν ℝ) (D : ι → Matrix κ ν ℝ) :
    0 ≤ inputBound T B D := by
  exact add_nonneg (mul_nonneg T.coe_nonneg (matrixSize_nonneg B))
    (mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun i _ ↦ matrixSize_nonneg (D i)))

/-- The actual F₀ random initial class is the genuine constant conditional
expectation lift; its conditional expectation is proved equal to itself. -/
theorem initial_eq_lift (T : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ) :
    initialH2 hξ hξ2 T = BSDEProcessLift.initialLift (𝓕:=𝓕) T (hξ2.toLp ξ) := by
  apply BSDEProcessLift.ext_ambient T
  have hce : μ[(hξ2.toLp ξ : Ω → ℝ) | 𝓕 0] =ᵐ[μ] ξ := by
    have hh := condExp_congr_ae (m:=𝓕 0) hξ2.coeFn_toLp
    rw [condExp_of_stronglyMeasurable (𝓕.le 0) hξ (hξ2.integrable one_le_two)] at hh
    exact hh
  have hi : (initialH2 hξ hξ2 T : ℝ≥0 × Ω → ℝ) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ]
      (fun z ↦ ξ z.2) := ae_of_ae_trim 𝓕.predictable_le_prod (initialH2_ae hξ hξ2 T)
  have hl : (BSDEProcessLift.initialLift (𝓕:=𝓕) T (hξ2.toLp ξ) : ℝ≥0 × Ω → ℝ) =ᵐ[
      (CommonItoCLM.timeMeasure_T T).prod μ]
      Function.uncurry (BSDEProcessLift.initialRaw (𝓕:=𝓕) (hξ2.toLp ξ)) :=
    ae_of_ae_trim 𝓕.predictable_le_prod (BSDEProcessLift.initialLift_ae T (hξ2.toLp ξ))
  filter_upwards [hi,hl,Measure.quasiMeasurePreserving_snd.ae hce] with z hi hl hc
  exact hi.trans (hc.symm.trans hl.symm)

/-- True random initial values have the expected sqrt(time) difference bound. -/
theorem initial_difference (T : ℝ≥0) {ξ ζ : Ω → ℝ}
    (hξ : StronglyMeasurable[𝓕 0] ξ) (hζ : StronglyMeasurable[𝓕 0] ζ)
    (hξ2 : MemLp ξ 2 μ) (hζ2 : MemLp ζ 2 μ) :
    ‖initialH2 hξ hξ2 T-initialH2 hζ hζ2 T‖ ≤
      Real.sqrt (T:ℝ)*‖hξ2.toLp ξ-hζ2.toLp ζ‖ := by
  rw [initial_eq_lift T hξ hξ2,initial_eq_lift T hζ hζ2,←BSDEProcessLift.initialLift_sub]
  exact BSDEProcessLift.initialLift_norm T _

variable {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

/-- Genuine input dependence of the assembled actual integral operator. -/
theorem picard_data_difference (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (η θ X : κ → H2 𝓕 μ T) (u v : ν → H2 𝓕 μ T) :
    ‖picardMap hW hWm hWc i₀ T A B C D η u X -
      picardMap hW hWm hWc i₀ T A B C D θ v X‖ ≤
      ‖η-θ‖ + inputBound T B D * ‖u-v‖ := by
  have he : picardMap hW hWm hWc i₀ T A B C D η u X -
      picardMap hW hWm hWc i₀ T A B C D θ v X =
      (η-θ) + (driftVector hWm i₀ T (matrixAction T B (u-v)) +
        ∑ i, itoVector hW hWm hWc i T (matrixAction T (D i) (u-v))) := by
    simp only [picardMap,map_add,map_sub,itoVector_add,itoVector_sub,
      Finset.sum_add_distrib,Finset.sum_sub_distrib]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add_right
  calc
    _ ≤ ‖driftVector hWm i₀ T (matrixAction T B (u-v))‖ +
        ‖∑ i, itoVector hW hWm hWc i T (matrixAction T (D i) (u-v))‖ := norm_add_le _ _
    _ ≤ (T:ℝ)*‖matrixAction T B (u-v)‖ +
        ∑ i, Real.sqrt (T:ℝ)*‖matrixAction T (D i) (u-v)‖ :=
      add_le_add (driftVector_norm_le hWm i₀ T _)
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ itoVector_norm_le hW hWm hWc i T _))
    _ ≤ (T:ℝ)*(matrixSize B*‖u-v‖) +
        ∑ i, Real.sqrt (T:ℝ)*(matrixSize (D i)*‖u-v‖) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left
          (((matrixAction T B).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (matrixAction_norm_le T B) (norm_nonneg _))) T.coe_nonneg
      · exact Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left
          (((matrixAction T (D i)).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (matrixAction_norm_le T (D i)) (norm_nonneg _))) (Real.sqrt_nonneg _)
    _ = _ := by simp only [inputBound,←Finset.mul_sum,←Finset.sum_mul]; ring

/-- Explicit actual fixed-point dependence, uniform over restarts. -/
theorem fixedPoint_difference (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (η θ X Y : κ → H2 𝓕 μ T) (u v : ν → H2 𝓕 μ T)
    (hc : CommonUniformHorizon.bound T A C < 1)
    (hX : picardMap hW hWm hWc i₀ T A B C D η u X = X)
    (hY : picardMap hW hWm hWc i₀ T A B C D θ v Y = Y) :
    ‖X-Y‖ ≤ (‖η-θ‖ + inputBound T B D*‖u-v‖)/(1-CommonUniformHorizon.bound T A C) := by
  have hh : ‖X-Y‖ ≤ CommonUniformHorizon.bound T A C*‖X-Y‖ +
      (‖η-θ‖ + inputBound T B D*‖u-v‖) := by
    calc
      _ = ‖picardMap hW hWm hWc i₀ T A B C D η u X -
        picardMap hW hWm hWc i₀ T A B C D θ v Y‖ := by rw [hX,hY]
      _ ≤ ‖picardMap hW hWm hWc i₀ T A B C D η u X -
          picardMap hW hWm hWc i₀ T A B C D η u Y‖ +
        ‖picardMap hW hWm hWc i₀ T A B C D η u Y -
          picardMap hW hWm hWc i₀ T A B C D θ v Y‖ := by
        simpa only [dist_eq_norm] using dist_triangle
          (picardMap hW hWm hWc i₀ T A B C D η u X)
          (picardMap hW hWm hWc i₀ T A B C D η u Y)
          (picardMap hW hWm hWc i₀ T A B C D θ v Y)
      _ ≤ _ := add_le_add
        ((picardMap_contraction hW hWm hWc i₀ T A B C D η X Y u).trans
          (mul_le_mul_of_nonneg_right (rate_le T A C) (norm_nonneg _)))
        (picard_data_difference hW hWm hWc i₀ T A B C D η θ Y u v)
  apply (le_div_iff₀ (sub_pos.mpr hc)).mpr
  nlinarith

include hWc in
/-- Quantitative dependence for arbitrary actual integral solutions, because
their genuine integral equations imply the proved Picard fixed-point equation. -/
theorem solution_difference (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ ζ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hζ : ∀ b, StronglyMeasurable[𝓕 0] (ζ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (hζ2 : ∀ b, MemLp (ζ b) 2 μ)
    (u v : ν → H2 𝓕 μ T) (q : Solution hW hWm T A B C D ξ u)
    (r : Solution hW hWm T A B C D ζ v)
    (hc : CommonUniformHorizon.bound T A C < 1) :
    ‖q.X-r.X‖ ≤
      (Real.sqrt (T:ℝ)*‖(fun b ↦ (hξ2 b).toLp (ξ b))-(fun b ↦ (hζ2 b).toLp (ζ b))‖ +
        inputBound T B D*‖u-v‖)/(1-CommonUniformHorizon.bound T A C) := by
  have hi : ‖(fun b ↦ initialH2 (hξ b) (hξ2 b) T)-
      (fun b ↦ initialH2 (hζ b) (hζ2 b) T)‖ ≤
      Real.sqrt (T:ℝ)*‖(fun b ↦ (hξ2 b).toLp (ξ b))-(fun b ↦ (hζ2 b).toLp (ζ b))‖ := by
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr
    intro b
    exact (initial_difference T (hξ b) (hζ b) (hξ2 b) (hζ2 b)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm
        ((fun b ↦ (hξ2 b).toLp (ξ b))-(fun b ↦ (hζ2 b).toLp (ζ b))) b) (Real.sqrt_nonneg _))
  exact (fixedPoint_difference hW hWm hWc i₀ T A B C D _ _ q.X r.X u v hc
    (CommonSolutionFixedPoint.solution_fixedPoint hW hWm hWc i₀ T A B C D ξ hξ hξ2 u q)
    (CommonSolutionFixedPoint.solution_fixedPoint hW hWm hWc i₀ T A B C D ζ hζ hζ2 v r)).trans
    (div_le_div_of_nonneg_right (add_le_add_left hi _) (sub_pos.mpr hc).le)

end LinearStochastic.CommonForwardBounds
