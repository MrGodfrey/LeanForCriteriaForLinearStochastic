import LinearStochastic.CommonFiltrationCompletion
import LinearStochastic.ProgressivePredictable

/-! Deterministic restarts on the original probability space and common
filtration. Only Brownian and measurability data are transported here; integral
concatenation is a separate statement. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonTimeShift
open MeasureTheory ProbabilityTheory Set
open CommonItoIsometry
open scoped NNReal
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The actual original filtration seen after deterministic time a. -/
def filtration (𝓕 : Filtration ℝ≥0 mΩ) (a : ℝ≥0) : Filtration ℝ≥0 mΩ where
  seq t := 𝓕 (a+t)
  mono' _ _ h := 𝓕.mono (add_le_add le_rfl h)
  le' t := 𝓕.le (a+t)

/-- Actual future increments, on the same Ω and measure. -/
def driver (W : ℝ≥0 → Ω → ℝ) (a : ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  W (a+t) ω - W a ω

instance complete (𝓕 : Filtration ℝ≥0 mΩ) [𝓕.IsComplete μ] (a : ℝ≥0) :
    (filtration 𝓕 a).IsComplete μ where
  measurableSet_of_null {_s} hs t := Filtration.IsComplete.measurableSet_of_null hs (a+t)

/-- Whole future-increment independence transports exactly, with no canonical
sample-space replacement and no assumed stochastic-integral property. -/
theorem forwardIndependent {W : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    [hF : ForwardIndependent W 𝓕 μ] (a : ℝ≥0) :
    ForwardIndependent (driver W a) (filtration 𝓕 a) μ where
  adapted t := (hF.adapted (a+t)).sub ((hF.adapted a).mono (𝓕.mono (le_add_right le_rfl)))
  indep s := by
    have he : (fun ω u ↦ driver W a (s+u) ω - driver W a s ω) =
        (fun ω u ↦ W ((a+s)+u) ω - W (a+s) ω) := by
      funext ω u
      simp only [driver,add_assoc]
      ring
    change Indep (𝓕 (a+s)) (MeasurableSpace.comap _ inferInstance) μ
    rw [he]
    exact hF.indep (a+s)

theorem preBrownian {W : ℝ≥0 → Ω → ℝ} (hW : IsPreBrownianReal W μ) (a : ℝ≥0) :
    IsPreBrownianReal (driver W a) μ := hW.shift a

theorem continuous_driver {W : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous fun t ↦ W t ω) (a : ℝ≥0) :
    ∀ ω, Continuous fun t ↦ driver W a t ω := fun ω ↦
  ((hc ω).comp (continuous_const.add continuous_id)).sub continuous_const

/-- Ordinary progressive controls remain progressive for the actual shifted
filtration, proved on the defining restricted product spaces. -/
theorem progressive {E : Type*} [MeasurableSpace E] {R : ℝ≥0 → Ω → E}
    {𝓕 : Filtration ℝ≥0 mΩ} (hR : IsProgressive 𝓕 R) (a : ℝ≥0) :
    IsProgressive (filtration 𝓕 a) (fun t ω ↦ R (a+t) ω) := by
  intro t
  have he : (fun p : Iic t × Ω ↦ R (a+p.1.val) p.2) =
      (fun p : Iic (a+t) × Ω ↦ R p.1.val p.2) ∘
        (fun p : Iic t × Ω ↦ ((⟨a+p.1.val,show a+p.1.val ≤ a+t from add_le_add le_rfl p.1.property⟩ : Iic (a+t)),p.2)) := rfl
  rw [he]
  exact (hR (a+t)).comp
    ((measurable_const.add (measurable_subtype_coe.comp measurable_fst)).subtype_mk.prodMk measurable_snd)

/-- The strong version also transports, without a separability assumption. -/
theorem stronglyProgressive {E : Type*} [TopologicalSpace E] {R : ℝ≥0 → Ω → E}
    {𝓕 : Filtration ℝ≥0 mΩ} (hR : IsStronglyProgressive 𝓕 R) (a : ℝ≥0) :
    IsStronglyProgressive (filtration 𝓕 a) (fun t ω ↦ R (a+t) ω) := by
  intro t
  have he : (fun p : Iic t × Ω ↦ R (a+p.1.val) p.2) =
      (fun p : Iic (a+t) × Ω ↦ R p.1.val p.2) ∘
        (fun p : Iic t × Ω ↦ ((⟨a+p.1.val,show a+p.1.val ≤ a+t from add_le_add le_rfl p.1.property⟩ : Iic (a+t)),p.2)) := rfl
  rw [he]
  exact (hR (a+t)).comp_measurable
    ((measurable_const.add (measurable_subtype_coe.comp measurable_fst)).subtype_mk.prodMk measurable_snd)
end LinearStochastic.CommonTimeShift
