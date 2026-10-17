module

public import LinearStochastic.ShiftedSwitchingGain
public import LinearStochastic.SwitchingFeedbackWindows
public import LinearStochastic.CommonDelayedSwitchingUniqueness
public import LinearStochastic.VectorHorizonRestriction

@[expose] public section

/-! The literal delayed feedback implies actual zero prefix and constant-gain
translated window relations. All exceptional endpoints are removed in time measure. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.ShiftedFeedbackWindows
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace
open CommonItoCLM CommonItoMultichannel SwitchingTimeMesh SwitchingFeedbackIdentity
variable {Ω E U κ τ : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)

/-- The literal zero waiting gain forces the true predictable prefix control to zero. -/
theorem prefix_zero (a δ T : ℝ≥0) (h : a+δ = T) (K : ℕ → E →L[ℝ] U)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (R : ℝ≥0 → Ω → E)
    (hf : (u : ℝ≥0 × Ω → U) =ᵐ[(timeMeasure_T T).prod μ]
      fun z => ShiftedSwitchingGain.gain a δ K z.1 (R z.1 z.2)) :
    VectorHorizonRestriction.restrict (show a ≤ T from h ▸ le_add_right le_rfl) u = 0 := by
  have ha : a ≤ T := h ▸ le_add_right le_rfl
  have hm : (timeMeasure_T a).prod μ ≤ (timeMeasure_T T).prod μ :=
    Measure.prod_mono (Measure.restrict_mono (Ioc_subset_Ioc_right ha) le_rfl) le_rfl
  have ht : ∀ᵐ z ∂(timeMeasure_T a).prod μ, z.1 < a :=
    Measure.quasiMeasurePreserving_fst.ae ((ae_away_mesh a).mono (fun _ ht => ht.1))
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
    𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
  filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod (VectorHorizonRestriction.restrict_ae ha u),
    hf.filter_mono (ae_mono hm),ht,ae_of_ae_trim 𝓕.predictable_le_prod
      (Lp.coeFn_zero U 2 (spacetimeMeasure 𝓕 μ a))] with z hu hf ht hz
  rw [hu,hf,ShiftedSwitchingGain.gain_before a δ K z.1 ht,hz]
  rfl

/-- Actual translated coefficient relation on every delayed dyadic interval. -/
theorem window (a δ T : ℝ≥0) (h : a+δ = T) (hδ : 0 < δ) (K : ℕ → E →L[ℝ] U)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (R : ℝ≥0 → Ω → E)
    (hR : (X : ℝ≥0 × Ω → E) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry R)
    (hf : (u : ℝ≥0 × Ω → U) =ᵐ[(timeMeasure_T T).prod μ]
      fun z => ShiftedSwitchingGain.gain a δ K z.1 (R z.1 z.2)) (j : ℕ) :
    VectorH2Extension.shift c (a+time δ j) (duration δ j) T (CommonDelayedSwitchingUniqueness.inside T a δ h j) u =
      (K j).compLp (VectorH2Extension.shift b (a+time δ j) (duration δ j) T (CommonDelayedSwitchingUniqueness.inside T a δ h j) X) := by
  have he : (u : ℝ≥0 × Ω → U) =ᵐ[(timeMeasure_T T).prod μ]
      fun z => ShiftedSwitchingGain.gain a δ K z.1 (X z) := by
    filter_upwards [hf,hR] with z hf hr
    exact hf.trans (congrArg (fun x : E => ShiftedSwitchingGain.gain a δ K z.1 x) hr).symm
  have hlocal := VectorH2Orthogonality.pull_ae (a+time δ j) (duration δ j) T
    (CommonDelayedSwitchingUniqueness.inside T a δ h j) he
  have ht : ∀ᵐ z ∂(timeMeasure_T (duration δ j)).prod μ, z.1 < duration δ j :=
    Measure.quasiMeasurePreserving_fst.ae ((ae_away_mesh (duration δ j)).mono (fun _ h => h.1))
  have hc := ae_of_ae_trim (CommonTimeShift.filtration 𝓕 (a+time δ j)).predictable_le_prod
    ((K j).coeFn_compLp (VectorH2Extension.shift b (a+time δ j) (duration δ j) T
      (CommonDelayedSwitchingUniqueness.inside T a δ h j) X))
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
    (CommonTimeShift.filtration 𝓕 (a+time δ j)).predictable_le_prod (Lp.stronglyMeasurable _)
  filter_upwards [VectorH2Extension.shift_ae c (a+time δ j) (duration δ j) T
      (CommonDelayedSwitchingUniqueness.inside T a δ h j) u,
    VectorH2Extension.shift_ae b (a+time δ j) (duration δ j) T
      (CommonDelayedSwitchingUniqueness.inside T a δ h j) X,hlocal,ht,hc] with z hu hx he ht hc
  have hmem : (a+time δ j)+z.1 ∈ Ico (a+time δ j) (a+time δ (j+1)) := by
    refine ⟨le_add_right le_rfl,?_⟩
    rw [←next_time,←add_assoc]
    exact add_lt_add_of_le_of_lt le_rfl ht
  rw [ShiftedSwitchingGain.gain_on a δ hδ K j ((a+time δ j)+z.1) hmem] at he
  exact hu.trans (he.trans ((congrArg (K j) hx).symm.trans hc.symm))

end LinearStochastic.ShiftedFeedbackWindows
