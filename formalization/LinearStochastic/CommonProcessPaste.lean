module

public import LinearStochastic.CommonProcessSpace
public import LinearStochastic.CommonTimeShift

@[expose] public section

/-! Measurable and continuous deterministic pasting on the original filtration. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonProcessPaste
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]

def paste (a : ℝ≥0) (R S : ℝ≥0 → Ω → E) (t : ℝ≥0) (ω : Ω) : E :=
  if t ≤ a then R t ω else S (t-a) ω

/-- Progressive processes paste in the actual original filtration when the
second process is progressive for F(a+·). -/
theorem progressive [MeasurableSpace E] {𝓕 : Filtration ℝ≥0 mΩ}
    (a : ℝ≥0) {R S : ℝ≥0 → Ω → E} (hR : IsProgressive 𝓕 R)
    (hS : IsProgressive (CommonTimeShift.filtration 𝓕 a) S) :
    IsProgressive 𝓕 (paste a R S) := by
  intro T
  by_cases hTa : T ≤ a
  · convert hR T using 1
    funext z
    exact if_pos (z.1.property.trans hTa)
  · have haT : a ≤ T := le_of_not_ge hTa
    have heF : CommonTimeShift.filtration 𝓕 a (T-a) = 𝓕 T := by
      change 𝓕 (a+(T-a)) = 𝓕 T
      rw [add_tsub_cancel_of_le haT]
    have hm := hS (T-a)
    rw [heF] at hm
    have hs : Measurable[Subtype.instMeasurableSpace.prod (𝓕 T)]
        (fun z : Iic T × Ω ↦ S (z.1.val-a) z.2) := by
      have he : (fun z : Iic T × Ω ↦ S (z.1.val-a) z.2) =
          (fun z : Iic (T-a) × Ω ↦ S z.1.val z.2) ∘
            (fun z : Iic T × Ω ↦ ((⟨z.1.val-a,tsub_le_tsub_right (show z.1.val ≤ T from z.1.property) a⟩ : Iic (T-a)),z.2)) := rfl
      rw [he]
      exact hm.comp (((measurable_subtype_coe.comp measurable_fst).sub measurable_const).subtype_mk.prodMk measurable_snd)
    exact Measurable.ite (measurableSet_le (measurable_subtype_coe.comp measurable_fst) measurable_const) (hR T) hs

/-- Continuity at the joining point follows from the actual endpoint identity. -/
theorem continuousOn [TopologicalSpace E] (a δ : ℝ≥0) (R S : ℝ≥0 → E)
    (hR : ContinuousOn R (Iic a)) (hS : ContinuousOn S (Iic δ)) (he : R a = S 0) :
    ContinuousOn (fun t ↦ if t ≤ a then R t else S (t-a)) (Iic (a+δ)) := by
  have hr : Continuous (fun t : ℝ≥0 ↦ R (min t a)) := by
    apply continuousOn_univ.mp
    exact hR.comp (continuous_id.min continuous_const).continuousOn
      (fun t _ ↦ min_le_right t a)
  have hs : Continuous (fun t : ℝ≥0 ↦ S (min (t-a) δ)) := by
    apply continuousOn_univ.mp
    exact hS.comp ((continuous_id.sub continuous_const).min continuous_const).continuousOn
      (fun t _ ↦ min_le_right (t-a) δ)
  have hc := hr.if_le hs continuous_id continuous_const (by
    intro t ht
    change t = a at ht
    subst t
    simpa only [min_self,tsub_self,zero_min] using he)
  apply hc.continuousOn.congr
  intro t ht
  by_cases hta : t ≤ a
  · simp only [id_eq,if_pos hta,min_eq_left hta]
  · have hsub : t-a ≤ δ := (tsub_le_iff_right).mpr (by simpa only [add_comm δ a] using (show t ≤ a+δ from ht))
    simp only [id_eq,if_neg hta,min_eq_left hsub]

omit mΩ in
/-- The endpoint of the original left process remains the pasted initial time. -/
theorem paste_zero (a : ℝ≥0) (R S : ℝ≥0 → Ω → E) : paste a R S 0 = R 0 := by
  funext ω
  exact if_pos zero_le

omit mΩ in
/-- The terminal value is the actual second process endpoint for a positive new interval. -/
theorem paste_terminal (a δ : ℝ≥0) (hδ : 0 < δ) (R S : ℝ≥0 → Ω → E) :
    paste a R S (a+δ) = S δ := by
  funext ω
  simp only [paste,not_le_of_gt (lt_add_of_pos_right a hδ),if_false,add_tsub_cancel_left]
/-- Pasting genuine continuous S² pieces preserves the whole-path L² bound.
The second path uses its own restarted clock and the same sample measure. -/
theorem paste_S2 (μ : Measure Ω) {𝓕 : Filtration ℝ≥0 mΩ}
    (a δ : ℝ≥0) {R S : ℝ≥0 → Ω → ℝ}
    (hR : IsProgressive 𝓕 R) (hS : IsProgressive (CommonTimeShift.filtration 𝓕 a) S)
    (hcR : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ R t ω) (Iic a))
    (hcS : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ S t ω) (Iic δ))
    (he : R a =ᵐ[μ] S 0)
    (h2R : MemLp (ContinuousDoobL2.pathSup R a) 2 μ)
    (h2S : MemLp (ContinuousDoobL2.pathSup S δ) 2 μ) :
    MemLp (ContinuousDoobL2.pathSup (paste a R S) (a+δ)) 2 μ := by
  letI : Nonempty (Iic (a+δ)) := ⟨⟨a+δ,show a+δ ≤ a+δ from le_rfl⟩⟩
  have hp := progressive a hR hS
  have hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ paste a R S t ω) (Iic (a+δ)) := by
    filter_upwards [hcR,hcS,he] with ω hr hs he
    exact continuousOn a δ (fun t ↦ R t ω) (fun t ↦ S t ω) hr hs he
  apply (h2R.add h2S).mono' (CommonStateS2.pathSup_measurableOn (a+δ) hp.isStronglyProgressive.stronglyAdapted hc)
  filter_upwards [hcR,hcS] with ω hr hs
  have hn : 0 ≤ ContinuousDoobL2.pathSup (paste a R S) (a+δ) ω := Real.iSup_nonneg fun _ ↦ norm_nonneg _
  change |ContinuousDoobL2.pathSup (paste a R S) (a+δ) ω| ≤ _
  rw [abs_of_nonneg hn]
  have hbR : BddAbove (range (fun t : Iic a ↦ ‖R t.val ω‖)) := by
    have hcomp : IsCompact (Iic a) := by rw [←Icc_bot]; exact isCompact_Icc
    simpa only [image_eq_range] using hcomp.bddAbove_image hr.norm
  have hbS : BddAbove (range (fun t : Iic δ ↦ ‖S t.val ω‖)) := by
    have hcomp : IsCompact (Iic δ) := by rw [←Icc_bot]; exact isCompact_Icc
    simpa only [image_eq_range] using hcomp.bddAbove_image hs.norm
  have hnR : 0 ≤ ContinuousDoobL2.pathSup R a ω := Real.iSup_nonneg fun _ ↦ norm_nonneg _
  have hnS : 0 ≤ ContinuousDoobL2.pathSup S δ ω := Real.iSup_nonneg fun _ ↦ norm_nonneg _
  apply ciSup_le
  intro t
  by_cases ht : t.val ≤ a
  · change ‖if t.val ≤ a then R t.val ω else S (t.val-a) ω‖ ≤ _
    rw [if_pos ht]
    exact (le_ciSup hbR ⟨t.val,ht⟩).trans (le_add_of_nonneg_right hnS)
  · have htd : t.val-a ≤ δ := tsub_le_iff_right.mpr (by simpa only [add_comm δ a] using (show t.val ≤ a+δ from t.property))
    change ‖if t.val ≤ a then R t.val ω else S (t.val-a) ω‖ ≤ _
    rw [if_neg ht]
    exact (le_ciSup hbS ⟨t.val-a,htd⟩).trans (le_add_of_nonneg_left hnR)

end LinearStochastic.CommonProcessPaste
