module

public import LinearStochastic.CommonDelayedSwitchingUniqueness
public import LinearStochastic.HilbertRestartUniqueness
public import LinearStochastic.ShiftedFeedbackWindows
public import LinearStochastic.HilbertSwitchingUniqueness

@[expose] public section

/-! Actual Hilbert uniqueness of the delayed singular feedback equation. Both controls
are permitted to differ; their literal raw feedback identities are converted to
actual zero-prefix and window classes; proved SDE uniqueness identifies the states. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.HilbertDelayedSwitchingUniqueness
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoCLM CommonItoMultichannel CommonVectorPicard CommonLocalSolution
open LpOrthonormalCoordinates VectorItoProduct LinearDuality SectionLinearDuality HilbertLocalSolution
open HilbertSectionCoordinates HilbertBrownianRealization HilbertRestartUniqueness SwitchingTimeMesh
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (i₀ : ι) (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E)
  (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
  (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
  (u v : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X Y : Lp E 2 (spacetimeMeasure 𝓕 μ T))
  (XT YT : Ω → E)
  (hX : SectionIntegralSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ (A.compLp X+B.compLp u)
    (fun i => (C i).compLp X+(D i).compLp u) X XT)
  (hY : SectionIntegralSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ (A.compLp Y+B.compLp v)
    (fun i => (C i).compLp Y+(D i).compLp v) Y YT)

include c i₀ hξ hξ2 hX hY in
/-- Genuine translated feedback equations identify the state classes even when
the two prescribed controls are different. -/
theorem state_unique (a δ : ℝ≥0) (h : a+δ = T)
    (hp : VectorHorizonRestriction.restrict (show a ≤ T from h ▸ le_add_right le_rfl) u =
      VectorHorizonRestriction.restrict (show a ≤ T from h ▸ le_add_right le_rfl) v)
    (K : ℕ → E →L[ℝ] U)
    (hu : ∀ j, VectorH2Extension.shift c (a+time δ j) (duration δ j) T (CommonDelayedSwitchingUniqueness.inside T a δ h j) u =
      (K j).compLp (VectorH2Extension.shift b (a+time δ j) (duration δ j) T (CommonDelayedSwitchingUniqueness.inside T a δ h j) X))
    (hv : ∀ j, VectorH2Extension.shift c (a+time δ j) (duration δ j) T (CommonDelayedSwitchingUniqueness.inside T a δ h j) v =
      (K j).compLp (VectorH2Extension.shift b (a+time δ j) (duration δ j) T (CommonDelayedSwitchingUniqueness.inside T a δ h j) Y)) : X = Y := by
  let q := coordinateSolution b c hW hWm i₀ T A B C D ξ hξ hξ2 u X XT hX
  let r := coordinateSolution b c hW hWm i₀ T A B C D ξ hξ hξ2 v Y YT hY
  have hqu j : (fun k => CommonShiftH2.shiftCLM (a+time δ j) (duration δ j) T (CommonDelayedSwitchingUniqueness.inside T a δ h j) (coordinate c k u)) =
      matrixAction (duration δ j) (coefficientMatrix c b (K j))
        (fun k => CommonShiftH2.shiftCLM (a+time δ j) (duration δ j) T (CommonDelayedSwitchingUniqueness.inside T a δ h j) (q.X k)) := by
    funext k
    rw [←coordinate_shift c T u,hu j,HilbertSwitchingUniqueness.coordinate_comp b c]
    simp only [coordinate_shift]
    rfl
  have hrv j : (fun k => CommonShiftH2.shiftCLM (a+time δ j) (duration δ j) T (CommonDelayedSwitchingUniqueness.inside T a δ h j) (coordinate c k v)) =
      matrixAction (duration δ j) (coefficientMatrix c b (K j))
        (fun k => CommonShiftH2.shiftCLM (a+time δ j) (duration δ j) T (CommonDelayedSwitchingUniqueness.inside T a δ h j) (r.X k)) := by
    funext k
    rw [←coordinate_shift c T v,hv j,HilbertSwitchingUniqueness.coordinate_comp b c]
    simp only [coordinate_shift]
    rfl
  have hp' : (fun k => CommonHorizonRestriction.restriction (hWm i₀)
      (show a ≤ T from h ▸ le_add_right le_rfl) (coordinate c k u)) =
      fun k => CommonHorizonRestriction.restriction (hWm i₀)
      (show a ≤ T from h ▸ le_add_right le_rfl) (coordinate c k v) := by
    funext k
    rw [←VectorHorizonRestriction.coordinate_restrict c hWm _ k i₀,
      ←VectorHorizonRestriction.coordinate_restrict c hWm _ k i₀,hp]
  have hqr := CommonDelayedSwitchingUniqueness.unique hW hWm i₀ T
    (coefficientMatrix b b A) (coefficientMatrix b c B)
    (fun i => coefficientMatrix b b (C i)) (fun i => coefficientMatrix b c (D i))
    (fun j ω => inner ℝ (b j) (ξ ω))
    (fun j => (innerSL ℝ (b j)).continuous.comp_stronglyMeasurable hξ)
    (fun j => (innerSL ℝ (b j)).comp_memLp' hξ2)
    (fun j => coordinate c j u) (fun j => coordinate c j v)
    q r a δ h (fun j => coefficientMatrix c b (K j)) hqu hrv hp'
  have heq : (fun j => coordinate b j X) = fun j => coordinate b j Y := by
    funext j
    have hm := CommonProgressiveComparison.product_ae_of_modification T (q.progressive j)
      (r.progressive j) (fun t ht => hqr.mono (fun ω hω => hω j t ht))
    apply Lp.ext
    apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
      𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
    exact (q.representative j).trans (hm.trans (r.representative j).symm)
  exact (assemble_coordinates (mΛ:=𝓕.predictable) b X).symm.trans
    ((congrArg (assemble (mΛ:=𝓕.predictable) b) heq).trans
      (assemble_coordinates (mΛ:=𝓕.predictable) b Y))

include c i₀ hξ hξ2 hX hY in
/-- Arbitrary actual continuous solutions with the literal singular raw feedback
are indistinguishable, including the terminal time. This theorem does not assume
equality of the two controls or uniqueness of a feedback solution. -/
theorem unique (a δ : ℝ≥0) (h : a+δ = T) (hδ : 0 < δ) (K : ℕ → E →L[ℝ] U) (R S : ℝ≥0 → Ω → E)
    (hR : (X : ℝ≥0 × Ω → E) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry R)
    (hS : (Y : ℝ≥0 × Ω → E) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry S)
    (hcR : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T))
    (hcS : ∀ᵐ ω ∂μ, ContinuousOn (fun t => S t ω) (Iic T))
    (hu : (u : ℝ≥0 × Ω → U) =ᵐ[(timeMeasure_T T).prod μ]
      (fun z => ShiftedSwitchingGain.gain a δ K z.1 (R z.1 z.2)))
    (hv : (v : ℝ≥0 × Ω → U) =ᵐ[(timeMeasure_T T).prod μ]
      (fun z => ShiftedSwitchingGain.gain a δ K z.1 (S z.1 z.2))) :
    X = Y ∧ u = v ∧ ∀ᵐ ω ∂μ, ∀ t, t ≤ T → R t ω = S t ω := by
  have hT : 0 < T := h ▸ zero_le.trans_lt (lt_add_of_pos_right a hδ)
  have hp := (ShiftedFeedbackWindows.prefix_zero a δ T h K u R hu).trans
    (ShiftedFeedbackWindows.prefix_zero a δ T h K v S hv).symm
  have hXY := state_unique b c hW hWm i₀ T A B C D ξ hξ hξ2 u v X Y XT YT hX hY a δ h hp K
    (ShiftedFeedbackWindows.window b c a δ T h hδ K u X R hR hu)
    (ShiftedFeedbackWindows.window b c a δ T h hδ K v Y S hS hv)
  have hp : Function.uncurry R =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry S := by
    rw [hXY] at hR
    exact hR.symm.trans hS
  refine ⟨hXY,?_,CommonContinuousUniqueness.indistinguishable_of_spacetime_ae μ T hT R S hcR hcS hp⟩
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
    𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
  filter_upwards [hu,hv,hp] with z hu hv hp
  exact hu.trans ((congrArg (fun x : E => ShiftedSwitchingGain.gain a δ K z.1 x) hp).trans hv.symm)

end LinearStochastic.HilbertDelayedSwitchingUniqueness
