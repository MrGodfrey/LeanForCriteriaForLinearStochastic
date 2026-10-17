module

public import LinearStochastic.CommonItoCLM
public import MathFin.Foundations.ItoIntegralCLM

@[expose] public section

noncomputable section
namespace LinearStochastic.CommonNaturalIntegral
open MeasureTheory ProbabilityTheory
open scoped NNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B μ) (hBm : ∀ t, Measurable (B t))

/-- The whole future process is independent of the actual scalar natural past. -/
def naturalForward : CommonItoIsometry.ForwardIndependent B
    (MathFin.ItoIntegralL2.natFiltration hBm) μ where
  adapted := (hB.isFilteredPreBrownian hBm).stronglyAdapted
  indep s := by
    have h := (hB.indepFun_shift s).symm
    apply indep_of_indep_of_le_left h
    refine iSup₂_le fun u hu => ?_
    have hBu : B u = (fun p : Set.Iic s → ℝ => p ⟨u,hu⟩) ∘
      (fun ω (t : Set.Iic s) => B t ω) := rfl
    rw [hBu,←MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

/-- The common-filtration integral specializes to the original scalar-natural
MathFin integral. Both are the same continuous extension of actual increments. -/
theorem common_eq_natural (T : ℝ≥0) :
    @CommonItoCLM.itoIntegralCLM_T Ω mΩ μ _ B
      (MathFin.ItoIntegralL2.natFiltration hBm) (naturalForward hB hBm) hB T hBm =
    MathFin.ItoIntegralCLM.itoIntegralCLM_T hB T hBm := by
  rfl

end LinearStochastic.CommonNaturalIntegral
