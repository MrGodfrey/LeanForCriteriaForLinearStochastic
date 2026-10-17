module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
public import Mathlib.Probability.Process.Predictable

@[expose] public section

noncomputable section
namespace LinearStochastic.TrimInclusion
open MeasureTheory
open scoped NNReal
variable {α : Type*} {m n : MeasurableSpace α} [m₀ : MeasurableSpace α]
  (ν : Measure α) (hm : m ≤ m₀) (hn : n ≤ m₀) (hmn : m ≤ n)

/-- The actual measurable-L² subspace inclusion preserves the ambient element. -/
def measurableInclusion : lpMeas ℝ ℝ m 2 ν →ₗᵢ[ℝ] lpMeas ℝ ℝ n 2 ν where
  toFun f := ⟨f.1, f.2.mono hmn⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

/-- Inclusion of actual trimmed L² spaces, using the canonical measurable-Lp
isometric equivalences; no arbitrary inclusion operator is supplied. -/
def inclusion : Lp ℝ 2 (ν.trim hm) →ₗᵢ[ℝ] Lp ℝ 2 (ν.trim hn) :=
  (lpMeasToLpTrimLie ℝ ℝ 2 ν hn).toLinearIsometry.comp
    ((measurableInclusion ν hmn).comp
      (lpMeasToLpTrimLie ℝ ℝ 2 ν hm).symm.toLinearIsometry)

theorem inclusion_ambient_ae (f : Lp ℝ 2 (ν.trim hm)) :
    (⇑(inclusion ν hm hn hmn f)) =ᵐ[ν] ⇑f := by
  exact (lpMeasToLpTrim_ae_eq hn
    (measurableInclusion ν hmn ((lpMeasToLpTrimLie ℝ ℝ 2 ν hm).symm f))).trans
    (lpTrimToLpMeas_ae_eq (𝕜 := ℝ) hm f)

/-- Predictability is monotone under inclusion of the given filtrations. -/
theorem predictable_mono {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {𝓕 𝓖 : Filtration ℝ≥0 mΩ} (h : 𝓕 ≤ 𝓖) : 𝓕.predictable ≤ 𝓖.predictable := by
  apply MeasurableSpace.generateFrom_le
  rintro s (⟨A,hA,rfl⟩ | ⟨t,A,hA,rfl⟩)
  · exact measurableSet_predictable_singleton_bot_prod (h 0 A hA)
  · exact measurableSet_predictable_Ioi_prod (h t A hA)

end LinearStochastic.TrimInclusion
