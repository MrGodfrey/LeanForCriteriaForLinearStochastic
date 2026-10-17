module

public import LinearStochastic.ShiftedSwitchingGain
public import LinearStochastic.VectorH2Extension
public import LinearStochastic.VectorH2Orthogonality

@[expose] public section

/-! Literal identification of a zero-extended local feedback with the
translated deterministic gain applied to the actual global state. -/
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.ShiftedFeedbackIdentity
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace
open CommonItoCLM CommonItoMultichannel
variable {Ω E U κ τ : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)

def feedback (a δ : ℝ≥0) (K : ℕ → E →L[ℝ] U) (R : ℝ≥0 → Ω → E) : ℝ≥0 → Ω → U :=
  fun t ω => ShiftedSwitchingGain.gain a δ K t (R t ω)

include b c in
theorem progressive (a δ : ℝ≥0) (K : ℕ → E →L[ℝ] U) (R : ℝ≥0 → Ω → E)
    (hR : IsStronglyProgressive 𝓕 R) : IsStronglyProgressive 𝓕 (feedback a δ K R) := by
  letI : FiniteDimensional ℝ E := b.toBasis.finiteDimensional_of_finite
  letI : FiniteDimensional ℝ U := c.toBasis.finiteDimensional_of_finite
  letI : MeasurableSpace (E →L[ℝ] U) := borel _
  have hg : StronglyMeasurable (ShiftedSwitchingGain.gain a δ K) :=
    (ShiftedSwitchingGain.measurable_gain a δ K).stronglyMeasurable
  intro t
  exact (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
    ((hg.comp_measurable (measurable_subtype_coe.comp measurable_fst)).prodMk (hR t))

variable {W : ℝ≥0 → Ω → ℝ} [CommonItoIsometry.ForwardIndependent W 𝓕 μ]
  (hWm : ∀ t, Measurable (W t))

omit [CompleteSpace U] in
theorem feedback_ae (a δ T : ℝ≥0) (h : a+δ = T) (K : ℕ → E →L[ℝ] U)
    (v : Lp U 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ))
    (Y : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ))
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (R S : ℝ≥0 → Ω → E)
    (hv : (v : ℝ≥0 × Ω → U) =ᵐ[(timeMeasure_T δ).prod μ]
      Function.uncurry (SwitchingFeedbackIdentity.feedback δ K S))
    (hY : (Y : ℝ≥0 × Ω → E) =ᵐ[(timeMeasure_T δ).prod μ] Function.uncurry S)
    (hX : (X : ℝ≥0 × Ω → E) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry R)
    (hshift : VectorH2Extension.shift b a δ T h.le X = Y) :
    (VectorH2Extension.extendShift c hWm a δ T h.le v : ℝ≥0 × Ω → U)
      =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (feedback a δ K R) := by
  have hl : ∀ᵐ z ∂(timeMeasure_T δ).prod μ,
      v z = SwitchingGain.gain δ K z.1 (R (a+z.1) z.2) := by
    have hs := VectorH2Extension.shift_ae b a δ T h.le X
    rw [hshift] at hs
    filter_upwards [hv,hY,hs,VectorH2Orthogonality.pull_ae a δ T h.le hX] with z hv hy hs hx
    change v z = SwitchingGain.gain δ K z.1 (S z.1 z.2) at hv
    rw [hv]
    exact congrArg (fun x : E => SwitchingGain.gain δ K z.1 x) (hy.symm.trans (hs.trans hx))
  have hw := VectorH2Extension.window_ae a δ T h.le
    (fun z => v z = SwitchingGain.gain δ K z.1 (R (a+z.1) z.2)) hl
  have hne : ∀ᵐ t ∂timeMeasure_T T, t ≠ a := by
    rw [ae_iff]
    simp only [not_not,Set.ofPred_eq_eq_singleton]
    rw [timeMeasure_T,Measure.restrict_apply (measurableSet_singleton a)]
    exact measure_mono_null Set.inter_subset_left (CommonItoL2.timeMeasure_singleton a)
  have ht : ∀ᵐ t ∂timeMeasure_T T, t ≤ T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
  filter_upwards [VectorH2Extension.extendShift_ae c hWm a δ T h.le v,hw,
    Measure.quasiMeasurePreserving_fst.ae hne,Measure.quasiMeasurePreserving_fst.ae ht]
    with z he hw hne ht
  change _ = ShiftedSwitchingGain.gain a δ K z.1 (R z.1 z.2)
  rw [he]
  by_cases ha : a ≤ z.1
  · have haz : a < z.1 := lt_of_le_of_ne ha hne.symm
    have hz : z.1 ≤ a+δ := h.symm ▸ ht
    rw [if_pos ⟨haz,hz⟩,ShiftedSwitchingGain.gain,if_pos ha]
    simpa only [add_tsub_cancel_of_le ha] using hw ⟨haz,hz⟩
  · rw [if_neg (fun hh => ha hh.1.le),ShiftedSwitchingGain.gain,if_neg ha]
    rfl

end LinearStochastic.ShiftedFeedbackIdentity
