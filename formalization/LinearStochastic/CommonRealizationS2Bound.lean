module

public import LinearStochastic.CommonIntegralS2Bound

@[expose] public section

/-! Quantitative S² control of the actual initial-plus-drift-plus-Itô path. -/
noncomputable section
namespace LinearStochastic.CommonRealizationS2Bound
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonVectorPicard CommonDriftS2 CommonStateS2 CommonPicardRealization ContinuousDoobL2
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ] [Fintype ι]
  {W : ι → ℝ≥0 → Ω → ℝ} [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t=>W i t ω)

include hW hWc in
/-- The actual continuous realization has a coefficient-free full-path bound
with the sharp standard constants sqrt(T) and 2 on its input integrands. -/
theorem realization_norm (i₀ : ι) (T : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (g : H2 𝓕 μ T) (σ : ι → H2 𝓕 μ T) :
    PathSupNorm.norm (μ:=μ) (realization hWm i₀ T ξ g σ) T ≤
      ‖hξ2.toLp ξ‖+Real.sqrt (T:ℝ)*‖g‖+2*∑ i, ‖σ i‖ := by
  let Z := CommonDriftPredictable.driftContinuousMod T (hWm i₀) g
  let Y := fun i=>CommonItoContinuous.itoContinuousMod T (hWm i) (σ i)
  have hset : Icc (0:ℝ≥0) T=Iic T := by ext t; simp
  have hZa : StronglyAdapted 𝓕 Z :=
    (CommonDriftPredictable.driftContinuousMod_isStronglyPredictable T (hWm i₀) g).isStronglyProgressive.stronglyAdapted
  have hZc : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>Z t ω) (Iic T) := by
    simpa only [hset] using CommonDriftPathwise.driftContinuousMod_continuousOn T (hWm i₀) g
  have hZ2 : MemLp (pathSup Z T) 2 μ := driftContinuousMod_S2 T (hWm i₀) g
  have hYa (i : ι) : StronglyAdapted 𝓕 (Y i) :=
    (CommonItoPredictable.itoContinuousMod_isStronglyPredictable (hW i) T (hWm i) (hWc i) (σ i)).isStronglyProgressive.stronglyAdapted
  have hYc (i : ι) : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>Y i t ω) (Iic T) := by
    simpa only [hset] using CommonItoContinuous.itoContinuousMod_continuousOn (hW i) T (hWm i) (hWc i) (σ i)
  have hY2 (i : ι) : MemLp (pathSup (Y i) T) 2 μ := itoContinuousMod_S2 hW hWm hWc i T (σ i)
  have hξa : StronglyAdapted 𝓕 (fun _=>ξ) := fun t=>hξ.mono (𝓕.mono (show (0:ℝ≥0)≤t from zero_le))
  have hξc : ∀ᵐ ω ∂μ, ContinuousOn (fun _ : ℝ≥0=>ξ ω) (Iic T) := ae_of_all _ (fun _=>continuousOn_const)
  have hfirst2 := pathSup_add_memLp T hξa hZa hξc hZc (constant_S2 T hξ2) hZ2
  have hfirstc : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>ξ ω+Z t ω) (Iic T) :=
    hZc.mono (fun _ h=>continuousOn_const.add h)
  have hsumc : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>∑ i,Y i t ω) (Iic T) := by
    have hall : ∀ᵐ ω ∂μ, ∀ i, ContinuousOn (fun t=>Y i t ω) (Iic T) := by rw [ae_all_iff]; exact hYc
    filter_upwards [hall] with ω hω
    exact continuousOn_finsetSum _ (fun i _=>hω i)
  have hsum2 := pathSup_sum_memLp Finset.univ T Y (fun i _=>hYa i) (fun i _=>hYc i) (fun i _=>hY2 i)
  have hfirst := PathSupNorm.add_le T (fun _=>ξ) Z hξc hZc (constant_S2 T hξ2) hZ2
  rw [PathSupNorm.constant T ξ hξ2] at hfirst
  have hsum := PathSupNorm.sum_le Finset.univ T Y (fun i _=>hYa i) (fun i _=>hYc i) (fun i _=>hY2 i)
  have hall := PathSupNorm.add_le T (fun t ω=>ξ ω+Z t ω) (fun t ω=>∑ i,Y i t ω) hfirstc hsumc hfirst2 hsum2
  apply hall.trans
  apply (add_le_add hfirst hsum).trans
  apply add_le_add
  · exact add_le_add le_rfl (CommonIntegralS2Bound.drift_norm hWm i₀ T g)
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _=>CommonIntegralS2Bound.ito_norm hW hWm hWc i T (σ i))

end LinearStochastic.CommonRealizationS2Bound
