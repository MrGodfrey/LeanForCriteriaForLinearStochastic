import LinearStochastic.CommonH2Paste

/-! Orthogonal time splitting of actual predictable spacetime L² classes. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonH2Split
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonShiftH2 CommonH2Paste CommonHorizonRestriction
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

omit [IsProbabilityMeasure μ] in
/-- The actual predictable L² squared norm is the ambient spacetime integral. -/
theorem norm_sq_ambient (T : ℝ≥0) (f : H2 𝓕 μ T) :
    ‖f‖^2 = ∫ z, (f z)^2 ∂(timeMeasure_T T).prod μ := by
  rw [lp_two_norm_sq]
  exact (integral_trim 𝓕.predictable_le_prod ((Lp.stronglyMeasurable f).pow 2)).symm

variable {W : ℝ≥0 → Ω → ℝ} [CommonItoIsometry.ForwardIndependent W 𝓕 μ]
  (hWm : ∀ t, Measurable (W t))

/-- True Pythagorean splitting across a deterministic joining time. -/
theorem norm_sq_split (a δ : ℝ≥0) (f : H2 𝓕 μ (a+δ)) :
    ‖f‖^2 = ‖restriction hWm (show a ≤ a+δ from le_add_right le_rfl) f‖^2 +
      ‖shiftCLM a δ (a+δ) le_rfl f‖^2 := by
  let ν := (timeMeasure.restrict (Ioc a (a+δ))).prod μ
  have hl : (timeMeasure_T a).prod μ ≤ (timeMeasure_T (a+δ)).prod μ :=
    Measure.prod_mono (Measure.restrict_mono (Ioc_subset_Ioc_right (show a ≤ a+δ from le_add_right le_rfl)) le_rfl) le_rfl
  have hr : ν ≤ (timeMeasure_T (a+δ)).prod μ :=
    Measure.prod_mono (CommonShiftMeasure.interval_le a δ (a+δ) le_rfl) le_rfl
  have hint := (memLp_two_iff_integrable_sq (ambient_memLp (a+δ) f).1).mp (ambient_memLp (a+δ) f)
  have hleft : ‖restriction hWm (show a ≤ a+δ from le_add_right le_rfl) f‖^2 =
      ∫ z, (f z)^2 ∂(timeMeasure_T a).prod μ := by
    rw [norm_sq_ambient]
    apply integral_congr_ae
    filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod (restriction_ae hWm (show a ≤ a+δ from le_add_right le_rfl) f)] with z hz
    rw [hz]
  have hright : ‖shiftCLM a δ (a+δ) le_rfl f‖^2 = ∫ z, (f z)^2 ∂ν := by
    rw [norm_sq_ambient]
    calc
      _ = ∫ z : ℝ≥0 × Ω, (f (a+z.1,z.2))^2 ∂(timeMeasure_T δ).prod μ :=
        integral_congr_ae ((shift_ae a δ (a+δ) le_rfl f).fun_comp (fun x : ℝ ↦ x^2))
      _ = _ := ((CommonShiftMeasure.add_interval a δ).prod (MeasurePreserving.id μ)).integral_comp
        (((continuous_const.add continuous_id : Continuous (fun t : ℝ≥0 ↦ a+t)).measurableEmbedding
          (fun _ _ h ↦ add_left_cancel h)).prodMap MeasurableEmbedding.id) (fun z ↦ (f z)^2)
  rw [hleft,hright,norm_sq_ambient,time_split,Measure.add_prod,integral_add_measure (hint.mono_measure hl) (hint.mono_measure hr)]

/-- Actual predictable classes are uniquely determined by their two pieces. -/
theorem ext_pieces (a δ : ℝ≥0) (f g : H2 𝓕 μ (a+δ))
    (hl : restriction hWm (show a ≤ a+δ from le_add_right le_rfl) f = restriction hWm (show a ≤ a+δ from le_add_right le_rfl) g)
    (hr : shiftCLM a δ (a+δ) le_rfl f = shiftCLM a δ (a+δ) le_rfl g) : f=g := by
  have hh := norm_sq_split hWm a δ (f-g)
  simp only [map_sub,hl,hr,sub_self,norm_zero,zero_pow (by decide : 2≠0),add_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (f-g)]))

include hWm

/-- The genuine concatenation has the sum of the two squared norms. -/
theorem paste_norm_sq (a δ : ℝ≥0) (f : H2 𝓕 μ a)
    (g : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) :
    ‖pasteH2 a δ f g‖^2 = ‖f‖^2+‖g‖^2 := by
  rw [norm_sq_split hWm,restriction_pasteH2 hWm,shift_pasteH2]

/-- Linearity is proved using actual restriction and shift, not assumed. -/
theorem paste_add (a δ : ℝ≥0) (f f' : H2 𝓕 μ a)
    (g g' : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) :
    pasteH2 a δ (f+f') (g+g') = pasteH2 a δ f g+pasteH2 a δ f' g' := by
  apply ext_pieces hWm a δ
  · rw [map_add,restriction_pasteH2 hWm,restriction_pasteH2 hWm,restriction_pasteH2 hWm]
  · rw [map_add,shift_pasteH2,shift_pasteH2,shift_pasteH2]

theorem paste_smul (a δ : ℝ≥0) (c : ℝ) (f : H2 𝓕 μ a)
    (g : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) :
    pasteH2 a δ (c • f) (c • g) = c • pasteH2 a δ f g := by
  apply ext_pieces hWm a δ
  · rw [map_smul,restriction_pasteH2 hWm,restriction_pasteH2 hWm]
  · rw [map_smul,shift_pasteH2,shift_pasteH2]
end LinearStochastic.CommonH2Split
