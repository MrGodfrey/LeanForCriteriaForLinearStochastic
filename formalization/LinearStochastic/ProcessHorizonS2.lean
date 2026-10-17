module

public import LinearStochastic.CommonStateS2

@[expose] public section

/-! True S² restriction to deterministic prefixes for vector processes. -/
noncomputable section
namespace LinearStochastic.ProcessHorizonS2
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open ContinuousDoobL2
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] {𝓕 : Filtration ℝ≥0 mΩ}

theorem prefix_memLp {t T : ℝ≥0} (h : t ≤ T) (R : ℝ≥0 → Ω → E)
    (ha : StronglyAdapted 𝓕 R)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun s => R s ω) (Iic T))
    (h2 : MemLp (pathSup R T) 2 μ) : MemLp (pathSup R t) 2 μ := by
  letI : Nonempty (Iic t) := ⟨⟨t,show t ≤ t from le_rfl⟩⟩
  have hct : ∀ᵐ ω ∂μ, ContinuousOn (fun s => R s ω) (Iic t) :=
    hc.mono (fun _ hω => hω.mono (Iic_subset_Iic.mpr h))
  apply h2.mono' (CommonStateS2.pathSup_measurableOn t ha hct)
  filter_upwards [hc] with ω hω
  change |pathSup R t ω| ≤ _
  have hn : 0 ≤ pathSup R t ω := Real.iSup_nonneg fun _ => norm_nonneg _
  rw [abs_of_nonneg hn]
  have hcomp : IsCompact (Iic T) := by rw [←Icc_bot]; exact isCompact_Icc
  have hb : BddAbove (range (fun s : Iic T => ‖R s.val ω‖)) := by
    simpa only [image_eq_range] using hcomp.bddAbove_image hω.norm
  apply ciSup_le
  intro s
  exact le_ciSup hb ⟨s.val,s.property.trans h⟩

end LinearStochastic.ProcessHorizonS2
