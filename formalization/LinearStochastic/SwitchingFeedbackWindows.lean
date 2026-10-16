import LinearStochastic.SwitchingFeedbackIdentity
import LinearStochastic.VectorH2Orthogonality

/-! The converse actual feedback bridge: an ordinary raw feedback identity
implies the genuine translated predictable L² class equation on each interval. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.SwitchingFeedbackWindows
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoL2 CommonItoCLM CommonItoMultichannel SwitchingTimeMesh SwitchingFeedbackIdentity
variable {Ω E U κ τ : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)

/-- The true raw feedback equation, together with the genuine state
representative, yields the constant-gain equation in every actual restart. -/
theorem window_of_feedback (T : ℝ≥0) (hT : 0 < T) (K : ℕ → E →L[ℝ] U)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (R : ℝ≥0 → Ω → E)
    (hR : (X : ℝ≥0 × Ω → E) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry R)
    (hf : (u : ℝ≥0 × Ω → U) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (feedback T K R))
    (j : ℕ) :
    VectorH2Extension.shift c (time T j) (duration T j) T (mesh_inside T j) u =
      (K j).compLp (VectorH2Extension.shift b (time T j) (duration T j) T (mesh_inside T j) X) := by
  have he : (u : ℝ≥0 × Ω → U) =ᵐ[(timeMeasure_T T).prod μ]
      fun z => SwitchingGain.gain T K z.1 (X z) := by
    filter_upwards [hf,hR] with z hf hr
    exact hf.trans (congrArg (fun x : E => SwitchingGain.gain T K z.1 x) hr).symm
  have hlocal := VectorH2Orthogonality.pull_ae (time T j) (duration T j) T (mesh_inside T j) he
  have ht : ∀ᵐ z ∂(timeMeasure_T (duration T j)).prod μ, z.1 < duration T j :=
    Measure.quasiMeasurePreserving_fst.ae ((ae_away_mesh (duration T j)).mono (fun _ h => h.1))
  have hc := ae_of_ae_trim (CommonTimeShift.filtration 𝓕 (time T j)).predictable_le_prod
    ((K j).coeFn_compLp (VectorH2Extension.shift b (time T j) (duration T j) T (mesh_inside T j) X))
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
    (CommonTimeShift.filtration 𝓕 (time T j)).predictable_le_prod (Lp.stronglyMeasurable _)
  filter_upwards [VectorH2Extension.shift_ae c (time T j) (duration T j) T (mesh_inside T j) u,
    VectorH2Extension.shift_ae b (time T j) (duration T j) T (mesh_inside T j) X,
    hlocal,ht,hc] with z hu hx he ht hc
  have hmem : time T j+z.1 ∈ Ico (time T j) (time T (j+1)) := by
    refine ⟨le_add_right le_rfl,?_⟩
    rw [←next_time]
    exact add_lt_add_of_le_of_lt le_rfl ht
  rw [SwitchingGain.gain_on T hT K j (time T j+z.1) hmem] at he
  exact hu.trans (he.trans ((congrArg (K j) hx).symm.trans hc.symm))

/-- Raw feedback and all genuine translated class equations are equivalent. -/
theorem feedback_ae_iff (T : ℝ≥0) (hT : 0 < T) (K : ℕ → E →L[ℝ] U)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (R : ℝ≥0 → Ω → E)
    (hR : (X : ℝ≥0 × Ω → E) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry R) :
    ((u : ℝ≥0 × Ω → U) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (feedback T K R)) ↔
      ∀ j, VectorH2Extension.shift c (time T j) (duration T j) T (mesh_inside T j) u =
        (K j).compLp (VectorH2Extension.shift b (time T j) (duration T j) T (mesh_inside T j) X) :=
  ⟨fun hf j => window_of_feedback b c T hT K u X R hR hf j,
    fun hw => feedback_ae b c T hT K u X R hR hw⟩

end LinearStochastic.SwitchingFeedbackWindows
