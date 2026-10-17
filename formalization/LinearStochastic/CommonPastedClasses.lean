module

public import LinearStochastic.CommonIntegralPaste

@[expose] public section

/-! Actual predictable classes of a pasted continuous process and linear matrix
coefficient compatibility. No state equation is assumed in these identities. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonPastedClasses
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonShiftH2
open CommonHorizonRestriction CommonProcessPaste
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent W 𝓕 μ]
  (hWm : ∀ t, Measurable (W t))

/-- The prefix class of the pasted raw process is the original prefix class. -/
theorem restriction_paste (a δ : ℝ≥0) (R S : ℝ≥0 → Ω → ℝ)
    (X : H2 𝓕 μ a) (Z : H2 𝓕 μ (a+δ))
    (hX : (X : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T a).prod μ] Function.uncurry R)
    (hZ : (Z : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T (a+δ)).prod μ] Function.uncurry (paste a R S)) :
    restriction hWm (show a ≤ a+δ from le_add_right le_rfl) Z = X := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable 𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
  have hm : (timeMeasure_T a).prod μ ≤ (timeMeasure_T (a+δ)).prod μ :=
    Measure.prod_mono (Measure.restrict_mono (show Ioc (0:ℝ≥0) a ⊆ Ioc 0 (a+δ) from fun t ht ↦ ⟨ht.1,ht.2.trans (le_add_right le_rfl)⟩) le_rfl) le_rfl
  have ht : ∀ᵐ t ∂timeMeasure_T a, t ≤ a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
  filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod (restriction_ae hWm (show a ≤ a+δ from le_add_right le_rfl) Z),
    hZ.filter_mono (ae_mono hm),hX,Measure.quasiMeasurePreserving_fst.ae ht] with z hr hz hx ht
  exact hr.trans (hz.trans ((if_pos ht).trans hx.symm))

/-- Positive restarted times lie strictly after the joining point, so the
translated class of the pasted process is exactly the second actual class. -/
theorem shift_paste (a δ : ℝ≥0) (R S : ℝ≥0 → Ω → ℝ)
    (Y : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) (Z : H2 𝓕 μ (a+δ))
    (hY : (Y : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T δ).prod μ] Function.uncurry S)
    (hZ : (Z : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T (a+δ)).prod μ] Function.uncurry (paste a R S)) :
    shiftCLM a δ (a+δ) le_rfl Z = Y := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
    (CommonTimeShift.filtration 𝓕 a).predictable_le_prod (Lp.stronglyMeasurable _)
  have ht : ∀ᵐ t ∂timeMeasure_T δ, 0 < t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.1
  filter_upwards [shift_ae a δ (a+δ) le_rfl Z,pull_ae a δ (a+δ) le_rfl hZ,hY,
    Measure.quasiMeasurePreserving_fst.ae ht] with z hs hz hy ht
  apply hs.trans (hz.trans _)
  change (if a+z.1 ≤ a then R (a+z.1) z.2 else S (a+z.1-a) z.2) = Y z
  rw [if_neg (not_le_of_gt (lt_add_of_pos_right a ht)),add_tsub_cancel_left]
  exact hy.symm

omit [IsProbabilityMeasure μ] in
/-- Every actual scalar linear operator commutes with literal finite matrix rows. -/
theorem map_matrixAction {𝓖 : Filtration ℝ≥0 mΩ} {κ ν : Type*} [Fintype κ] [Fintype ν]
    (t T : ℝ≥0) (L : H2 𝓕 μ T →L[ℝ] H2 𝓖 μ t)
    (A : Matrix κ ν ℝ) (X : ν → H2 𝓕 μ T) (a : κ) :
    L (matrixAction T A X a) = matrixAction t A (fun b ↦ L (X b)) a := by
  simp only [matrixAction_apply,map_sum,map_smul]

omit [IsProbabilityMeasure μ] in
/-- The same genuine commutation applies to state and control coefficient sums. -/
theorem map_linearInput {𝓖 : Filtration ℝ≥0 mΩ} {κ ν : Type*} [Fintype κ] [Fintype ν]
    (t T : ℝ≥0) (L : H2 𝓕 μ T →L[ℝ] H2 𝓖 μ t)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (X : κ → H2 𝓕 μ T) (u : ν → H2 𝓕 μ T) (a : κ) :
    L (CommonLocalSolution.driftInput T A B u X a) =
      CommonLocalSolution.driftInput t A B (fun b ↦ L (u b)) (fun b ↦ L (X b)) a := by
  simp only [CommonLocalSolution.driftInput,Pi.add_apply,map_add,map_matrixAction]
end LinearStochastic.CommonPastedClasses
