module

public import LinearStochastic.CommonPastedClasses

@[expose] public section

/-! Actual predictable L² concatenation on the original sample space. The second
piece uses the shifted filtration F(a+·). No path continuity is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonH2Paste
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open CommonItoL2 CommonItoCLM CommonShiftH2 CommonProcessPaste CommonVectorPicard
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- Subtraction takes the actual translated interval back to its local clock. -/
theorem sub_interval (a δ : ℝ≥0) :
    MeasurePreserving (fun t : ℝ≥0 ↦ t-a)
      (timeMeasure.restrict (Ioc a (a+δ))) (timeMeasure_T δ) := by
  refine ⟨measurable_id.sub measurable_const,?_⟩
  rw [←(CommonShiftMeasure.add_interval a δ).map_eq,
    Measure.map_map (show Measurable (fun t : ℝ≥0 ↦ t-a) from measurable_id.sub measurable_const)
      (show Measurable (fun t : ℝ≥0 ↦ a+t) from measurable_const.add measurable_id)]
  have he : (fun t : ℝ≥0 ↦ t-a) ∘ (fun t ↦ a+t) = id := by
    funext t
    exact add_tsub_cancel_left a t
  rw [he,Measure.map_id]

/-- The two half-open intervals form exactly the global time measure. -/
theorem time_split (a δ : ℝ≥0) :
    timeMeasure_T (a+δ) = timeMeasure_T a + timeMeasure.restrict (Ioc a (a+δ)) := by
  change timeMeasure.restrict (Ioc 0 (a+δ)) = _
  rw [←Ioc_union_Ioc_eq_Ioc (show (0:ℝ≥0) ≤ a from zero_le) (show a ≤ a+δ from le_add_right le_rfl)]
  exact Measure.restrict_union (by
    apply disjoint_left.mpr
    intro t ht hs
    exact (not_lt_of_ge ht.2) hs.1) measurableSet_Ioc

/-- Pasting square-integrable raw pieces preserves actual spacetime L². -/
theorem raw_memLp (a δ : ℝ≥0) (R S : ℝ≥0 → Ω → ℝ)
    (hR : MemLp (Function.uncurry R) 2 ((timeMeasure_T a).prod μ))
    (hS : MemLp (Function.uncurry S) 2 ((timeMeasure_T δ).prod μ)) :
    MemLp (Function.uncurry (paste a R S)) 2 ((timeMeasure_T (a+δ)).prod μ) := by
  have hl : MemLp (Function.uncurry (paste a R S)) 2 ((timeMeasure_T a).prod μ) := by
    apply hR.ae_eq
    have ht : ∀ᵐ t ∂timeMeasure_T a, t ≤ a := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae ht] with z ht
    exact (if_pos ht).symm
  have hr : MemLp (Function.uncurry (paste a R S)) 2
      ((timeMeasure.restrict (Ioc a (a+δ))).prod μ) := by
    have hs := hS.comp_measurePreserving ((sub_interval a δ).prod (MeasurePreserving.id μ))
    apply hs.ae_eq
    have ht : ∀ᵐ t ∂timeMeasure.restrict (Ioc a (a+δ)), ¬t ≤ a := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using not_le_of_gt ht.1
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae ht] with z ht
    exact (if_neg ht).symm
  rw [time_split,Measure.add_prod]
  apply (memLp_two_iff_integrable_sq (hl.aestronglyMeasurable.add_measure hr.aestronglyMeasurable)).mpr
  exact (memLp_two_iff_integrable_sq hl.aestronglyMeasurable).mp hl |>.add_measure
    ((memLp_two_iff_integrable_sq hr.aestronglyMeasurable).mp hr)

/-- An actual predictable class representing the raw two-piece process. -/
def pasteH2 (a δ : ℝ≥0) (f : H2 𝓕 μ a)
    (g : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) : H2 𝓕 μ (a+δ) :=
  (ProgressivePredictable.exists_predictable_Lp_of_progressive μ
    (progressive a
      (show IsStronglyPredictable 𝓕 (fun t ω ↦ f (t,ω)) from Lp.stronglyMeasurable f).isStronglyProgressive.isProgressive
      (show IsStronglyPredictable (CommonTimeShift.filtration 𝓕 a) (fun t ω ↦ g (t,ω)) from Lp.stronglyMeasurable g).isStronglyProgressive.isProgressive)
    (a+δ) 2 (raw_memLp a δ (fun t ω ↦ f (t,ω)) (fun t ω ↦ g (t,ω))
      (ambient_memLp a f) (ambient_memLp δ g))).choose

theorem pasteH2_ae (a δ : ℝ≥0) (f : H2 𝓕 μ a)
    (g : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) :
    (pasteH2 a δ f g : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T (a+δ)).prod μ]
      Function.uncurry (paste a (fun t ω ↦ f (t,ω)) (fun t ω ↦ g (t,ω))) :=
  (ProgressivePredictable.exists_predictable_Lp_of_progressive μ
    (progressive a
      (show IsStronglyPredictable 𝓕 (fun t ω ↦ f (t,ω)) from Lp.stronglyMeasurable f).isStronglyProgressive.isProgressive
      (show IsStronglyPredictable (CommonTimeShift.filtration 𝓕 a) (fun t ω ↦ g (t,ω)) from Lp.stronglyMeasurable g).isStronglyProgressive.isProgressive)
    (a+δ) 2 (raw_memLp a δ (fun t ω ↦ f (t,ω)) (fun t ω ↦ g (t,ω))
      (ambient_memLp a f) (ambient_memLp δ g))).choose_spec

/-- Restricting the genuine concatenation recovers its original first piece. -/
theorem restriction_pasteH2 {W : ℝ≥0 → Ω → ℝ}
    [CommonItoIsometry.ForwardIndependent W 𝓕 μ]
    (hWm : ∀ t, Measurable (W t)) (a δ : ℝ≥0) (f : H2 𝓕 μ a)
    (g : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) :
    CommonHorizonRestriction.restriction hWm (show a ≤ a+δ from le_add_right le_rfl)
      (pasteH2 a δ f g) = f :=
  CommonPastedClasses.restriction_paste hWm a δ _ _ f _ Filter.EventuallyEq.rfl (pasteH2_ae a δ f g)

/-- Translating the second piece back to its local clock recovers it exactly. -/
theorem shift_pasteH2 (a δ : ℝ≥0) (f : H2 𝓕 μ a)
    (g : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) :
    shiftCLM a δ (a+δ) le_rfl (pasteH2 a δ f g) = g :=
  CommonPastedClasses.shift_paste a δ _ _ g _ Filter.EventuallyEq.rfl (pasteH2_ae a δ f g)

end LinearStochastic.CommonH2Paste
