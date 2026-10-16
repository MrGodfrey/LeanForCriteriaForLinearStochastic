import LinearStochastic.SwitchingGain
import LinearStochastic.VectorH2Extension

/-! The actual window feedback equations determine the total control as the
literal deterministic gain applied to the same state. Mesh endpoints are
removed using the genuine atomless time measure, not a pointwise convention. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.SwitchingFeedbackIdentity
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoL2 CommonItoCLM CommonItoMultichannel SwitchingTimeMesh
variable {Ω E U κ τ : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)

/-- The literal raw feedback associated with the deterministic half-open gain. -/
def feedback (T : ℝ≥0) (K : ℕ → E →L[ℝ] U) (R : ℝ≥0 → Ω → E) : ℝ≥0 → Ω → U :=
  fun t ω => SwitchingGain.gain T K t (R t ω)

include b c in
/-- Deterministic Borel gains preserve ordinary strong progressiveness. -/
theorem feedback_progressive (T : ℝ≥0) (K : ℕ → E →L[ℝ] U) (R : ℝ≥0 → Ω → E)
    (hR : IsStronglyProgressive 𝓕 R) : IsStronglyProgressive 𝓕 (feedback T K R) := by
  letI : FiniteDimensional ℝ E := b.toBasis.finiteDimensional_of_finite
  letI : FiniteDimensional ℝ U := c.toBasis.finiteDimensional_of_finite
  letI : MeasurableSpace (E →L[ℝ] U) := borel _
  have hg : StronglyMeasurable (SwitchingGain.gain T K) := (SwitchingGain.measurable_gain T K).stronglyMeasurable
  intro t
  exact (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
    ((hg.comp_measurable (measurable_subtype_coe.comp measurable_fst)).prodMk (hR t))

/-- All mesh points, including the final endpoint, have zero time measure. -/
theorem ae_away_mesh (T : ℝ≥0) :
    ∀ᵐ t ∂timeMeasure_T T, t < T ∧ ∀ j, t ≠ time T j := by
  have hz (s : ℝ≥0) : timeMeasure_T T {s} = 0 := by
    rw [timeMeasure_T,Measure.restrict_apply (measurableSet_singleton s)]
    exact measure_mono_null Set.inter_subset_left (timeMeasure_singleton s)
  have hn (s : ℝ≥0) : ∀ᵐ t ∂timeMeasure_T T, t ≠ s := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_eq_eq_singleton] using hz s
  have hall : ∀ᵐ t ∂timeMeasure_T T, ∀ j, t ≠ time T j := by
    rw [ae_all_iff]
    exact fun j => hn (time T j)
  filter_upwards [ae_restrict_mem measurableSet_Ioc,hn T,hall] with t ht hne hall
  exact ⟨lt_of_le_of_ne ht.2 hne,hall⟩


/-- The actual dyadic window is contained in the global horizon. -/
theorem mesh_inside (T : ℝ≥0) (j : ℕ) : time T j+duration T j ≤ T := by
  rw [next_time]
  exact time_le T (j+1)

omit [CompleteSpace U] in
/-- Actual translated L² feedback equations on all windows imply the literal
raw gain-times-state identity in ambient time-probability product measure. -/
theorem feedback_ae (T : ℝ≥0) (hT : 0 < T) (K : ℕ → E →L[ℝ] U)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (R : ℝ≥0 → Ω → E)
    (hR : (X : ℝ≥0 × Ω → E) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry R)
    (hfeedback : ∀ j, VectorH2Extension.shift c (time T j) (duration T j) T (mesh_inside T j) u =
      (K j).compLp (VectorH2Extension.shift b (time T j) (duration T j) T (mesh_inside T j) X)) :
    (u : ℝ≥0 × Ω → U) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (feedback T K R) := by
  have hw (j : ℕ) : ∀ᵐ z ∂(timeMeasure_T T).prod μ,
      time T j < z.1 ∧ z.1 ≤ time T j+duration T j → u z = K j (X z) := by
    have hl : ∀ᵐ z ∂(timeMeasure_T (duration T j)).prod μ,
        u (time T j+z.1,z.2) = K j (X (time T j+z.1,z.2)) := by
      have hc := ae_of_ae_trim (CommonTimeShift.filtration 𝓕 (time T j)).predictable_le_prod
        ((K j).coeFn_compLp (VectorH2Extension.shift b (time T j) (duration T j) T (mesh_inside T j) X))
      filter_upwards [VectorH2Extension.shift_ae c (time T j) (duration T j) T (mesh_inside T j) u,
        VectorH2Extension.shift_ae b (time T j) (duration T j) T (mesh_inside T j) X,hc]
        with z hu hx hc
      exact hu.symm.trans ((congrArg (fun f : Lp U 2
        (spacetimeMeasure (CommonTimeShift.filtration 𝓕 (time T j)) μ (duration T j)) => f z)
        (hfeedback j)).trans (hc.trans (congrArg (K j) hx)))
    have hh := VectorH2Extension.window_ae (time T j) (duration T j) T (mesh_inside T j)
      (fun z => u (time T j+z.1,z.2) = K j (X (time T j+z.1,z.2))) hl
    filter_upwards [hh] with z hz
    intro ht
    simpa only [add_tsub_cancel_of_le ht.1.le] using hz ht
  have hall : ∀ᵐ z ∂(timeMeasure_T T).prod μ, ∀ j,
      time T j < z.1 ∧ z.1 ≤ time T j+duration T j → u z = K j (X z) := by
    rw [ae_all_iff]
    exact hw
  filter_upwards [hall,hR,Measure.quasiMeasurePreserving_fst.ae (ae_away_mesh T)] with z hz hr ht
  obtain ⟨j,hj⟩ := SwitchingGain.covers T z.1 ht.1
  have hj0 : time T j < z.1 := lt_of_le_of_ne hj.1 (ht.2 j).symm
  have hj1 : z.1 ≤ time T j+duration T j := by rw [next_time]; exact hj.2.le
  change u z = SwitchingGain.gain T K z.1 (R z.1 z.2)
  rw [SwitchingGain.gain_on T hT K j z.1 hj]
  exact (hz j ⟨hj0,hj1⟩).trans (congrArg (K j) hr)


/-- The literal feedback is an ordinary progressive, square-integrable control;
its square integrability comes from the actual constructed total control. -/
theorem feedback_admissible (T : ℝ≥0) (hT : 0 < T) (K : ℕ → E →L[ℝ] U)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (R : ℝ≥0 → Ω → E) (hp : IsStronglyProgressive 𝓕 R)
    (hR : (X : ℝ≥0 × Ω → E) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry R)
    (hfeedback : ∀ j, VectorH2Extension.shift c (time T j) (duration T j) T (mesh_inside T j) u =
      (K j).compLp (VectorH2Extension.shift b (time T j) (duration T j) T (mesh_inside T j) X)) :
    IsStronglyProgressive 𝓕 (feedback T K R) ∧
      MemLp (Function.uncurry (feedback T K R)) 2 ((timeMeasure_T T).prod μ) := by
  refine ⟨feedback_progressive b c T K R hp,?_⟩
  exact (memLp_congr_ae (feedback_ae b c T hT K u X R hR hfeedback)).mp
    (memLp_of_memLp_trim 𝓕.predictable_le_prod (Lp.memLp u))

end LinearStochastic.SwitchingFeedbackIdentity
