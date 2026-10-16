import LinearStochastic.CommonVectorPicard
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

/-! Actual F₀-measurable square-integrable random initial values, embedded as
constant-in-time predictable processes, and their controlled matrix Picard
fixed point. No initial-value or integral identity is hidden in a structure. -/
noncomputable section
namespace LinearStochastic.CommonInitialPredictable
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open CommonItoMultichannel CommonVectorPicard
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- A genuine F₀-measurable random variable is a predictable constant process. -/
theorem initial_predictable {ξ : Ω → ℝ} (hξ : StronglyMeasurable[𝓕 0] ξ) :
    IsStronglyPredictable 𝓕 (fun _ ω ↦ ξ ω) := by
  have ha : StronglyAdapted 𝓕 (fun _ ω ↦ ξ ω) := fun t ↦ hξ.mono (𝓕.mono (show (0 : ℝ≥0) ≤ t from zero_le))
  exact ha.isStronglyPredictable_of_leftContinuous fun _ _ ↦ continuousWithinAt_const

/-- The actual initial random variable has finite predictable space-time L²
norm on every bounded horizon. -/
theorem initial_memLp {ξ : Ω → ℝ} (hξ : StronglyMeasurable[𝓕 0] ξ)
    (hξ2 : MemLp ξ 2 μ) (T : ℝ≥0) :
    MemLp (fun z : ℝ≥0 × Ω ↦ ξ z.2) 2 (spacetimeMeasure 𝓕 μ T) := by
  have hp := initial_predictable hξ
  change StronglyMeasurable[𝓕.predictable] (fun z : ℝ≥0 × Ω ↦ ξ z.2) at hp
  have hm := hξ2.comp_snd (CommonItoCLM.timeMeasure_T T)
  refine ⟨hp.aestronglyMeasurable, ?_⟩
  change eLpNorm (fun z : ℝ≥0 × Ω ↦ ξ z.2) 2
    (((CommonItoCLM.timeMeasure_T T).prod μ).trim 𝓕.predictable_le_prod) < ⊤
  rw [eLpNorm_trim _ hp]
  exact hm.eLpNorm_lt_top

def initialH2 {ξ : Ω → ℝ} (hξ : StronglyMeasurable[𝓕 0] ξ)
    (hξ2 : MemLp ξ 2 μ) (T : ℝ≥0) : H2 𝓕 μ T :=
  (initial_memLp hξ hξ2 T).toLp (fun z : ℝ≥0 × Ω ↦ ξ z.2)

theorem initialH2_ae {ξ : Ω → ℝ} (hξ : StronglyMeasurable[𝓕 0] ξ)
    (hξ2 : MemLp ξ 2 μ) (T : ℝ≥0) :
    initialH2 hξ hξ2 T =ᵐ[spacetimeMeasure 𝓕 μ T] (fun z : ℝ≥0 × Ω ↦ ξ z.2) :=
  (initial_memLp hξ hξ2 T).coeFn_toLp

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

/-- Genuine short-horizon controlled matrix integral fixed point with an
arbitrary actual square-integrable F₀ random initial state. Equality here is
in predictable H²; continuous pathwise realization is a separate theorem. -/
theorem exists_unique_initial_fixedPoint (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ a, StronglyMeasurable[𝓕 0] (ξ a))
    (hξ2 : ∀ a, MemLp (ξ a) 2 μ) (u : ν → H2 𝓕 μ T)
    (hc : rate (𝓕:=𝓕) (μ:=μ) T A C < 1) :
    ∃! X, picardMap hW hWm hWc i₀ T A B C D (fun a ↦ initialH2 (hξ a) (hξ2 a) T) u X = X :=
  exists_unique_fixedPoint hW hWm hWc i₀ T A B C D _ u hc

end LinearStochastic.CommonInitialPredictable
