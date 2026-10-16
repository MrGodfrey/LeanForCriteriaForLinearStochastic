import LinearStochastic.CommonFiltrationCompletion

noncomputable section
namespace LinearStochastic.CommonNullL2
open MeasureTheory ProbabilityTheory CommonNullAugmentation
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Adjoining ambient null events adds no actual L² random variables modulo
almost-everywhere equality. The proof uses true conditional expectations. -/
theorem measurable_of_null_augmented {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (F : Lp ℝ 2 μ) (hF : AEStronglyMeasurable[m ⊔ nullsAlg mΩ μ] F μ) :
    AEStronglyMeasurable[m] F μ := by
  have ha : m ⊔ nullsAlg mΩ μ ≤ mΩ := sup_le hm nullsAlg_le
  have he : μ[(F : Ω → ℝ) | m] =ᵐ[μ] F :=
    (condExp_sup_nulls hm ((Lp.memLp F).integrable one_le_two)).symm.trans
      (condExp_of_aestronglyMeasurable' ha hF ((Lp.memLp F).integrable one_le_two))
  exact stronglyMeasurable_condExp.aestronglyMeasurable.congr he

end LinearStochastic.CommonNullL2
