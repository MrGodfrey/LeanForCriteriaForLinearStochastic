import LinearStochastic.RealTimeBridge
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
namespace LinearStochastic.CommonContinuousUniqueness
open MeasureTheory MeasureTheory.Measure Set
open scoped NNReal
variable {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [T2Space E]

/-- Actual Lebesgue-a.e. equality of continuous nonnegative-time paths extends
to both endpoints of a nondegenerate finite interval. -/
theorem path_eq_of_time_ae (T : ℝ≥0) (hT : 0 < T) (X Y : ℝ≥0 → E)
    (hX : ContinuousOn X (Iic T)) (hY : ContinuousOn Y (Iic T))
    (hXY : X =ᵐ[CommonItoCLM.timeMeasure_T T] Y) : EqOn X Y (Iic T) := by
  have hreal := (RealTimeBridge.toNNReal_measurePreserving T).quasiMeasurePreserving.ae hXY
  have hmap : MapsTo Real.toNNReal (Icc (0 : ℝ) (T : ℝ)) (Iic T) := by
    intro x hx
    exact Real.toNNReal_le_iff_le_coe.mpr hx.2
  have hXr : ContinuousOn (fun x : ℝ => X x.toNNReal) (Icc 0 (T : ℝ)) :=
    hX.comp continuous_real_toNNReal.continuousOn hmap
  have hYr : ContinuousOn (fun x : ℝ => Y x.toNNReal) (Icc 0 (T : ℝ)) :=
    hY.comp continuous_real_toNNReal.continuousOn hmap
  have hcc : (fun x : ℝ => X x.toNNReal) =ᵐ[volume.restrict (Icc 0 (T : ℝ))]
      (fun x => Y x.toNNReal) := by
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc.symm]
    exact hreal
  have hne : (0 : ℝ) ≠ (T : ℝ) := ne_of_lt (by exact_mod_cast hT)
  have he := eqOn_Icc_of_ae_eq volume hne hcc hXr hYr
  intro t ht
  simpa only [Real.toNNReal_coe] using he
    (show (t : ℝ) ∈ Icc 0 (T : ℝ) from ⟨t.coe_nonneg,by exact_mod_cast ht⟩)

/-- Equality of genuine spacetime classes and almost surely continuous paths
gives a single probability-one set on which every time, including 0 and T,
agrees. Separate fixed-time exceptional sets are not assumed sufficient. -/
theorem indistinguishable_of_spacetime_ae
    (μ : Measure Ω) [SFinite μ] (T : ℝ≥0) (hT : 0 < T)
    (X Y : ℝ≥0 → Ω → E)
    (hX : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Iic T))
    (hY : ∀ᵐ ω ∂μ, ContinuousOn (fun t => Y t ω) (Iic T))
    (hXY : Function.uncurry X =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry Y) :
    ∀ᵐ ω ∂μ, ∀ t, t ≤ T → X t ω = Y t ω := by
  have hs := ae_ae_of_ae_prod (measurePreserving_swap.quasiMeasurePreserving.ae hXY)
  filter_upwards [hX,hY,hs] with ω hX hY he
  exact path_eq_of_time_ae T hT (fun t => X t ω) (fun t => Y t ω) hX hY he

#print axioms indistinguishable_of_spacetime_ae
end LinearStochastic.CommonContinuousUniqueness
