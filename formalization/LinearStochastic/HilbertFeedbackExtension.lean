module

public import LinearStochastic.HilbertNullExtension
public import LinearStochastic.ShiftedFeedbackIdentity
public import LinearStochastic.RawPathOfRepresentative

@[expose] public section

/-! Extending an actual short-horizon feedback construction by an uncontrolled
prefix yields the literal translated deterministic feedback on the whole
original probability space and original time interval. -/
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.HilbertFeedbackExtension
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
open CommonItoMultichannel SectionLinearDuality LinearDuality VectorHorizonRestriction ProgressiveControlSection
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι]
  (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

local instance shiftedForwardFamily (a : ℝ≥0) :
    ∀ i, CommonItoIsometry.ForwardIndependent (fun t ω => W i (a+t) ω-W i a ω)
      (CommonTimeShift.filtration 𝓕 a) μ := fun _ => CommonTimeShift.forwardIndependent a

include c in
theorem exists_feedback (i₀ : ι) (a δ T : ℝ≥0) (h : a+δ = T)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (K : ℕ → E →L[ℝ] U)
    (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (hnull : ∀ η : Ω → E, StronglyMeasurable[(CommonTimeShift.filtration 𝓕 a) 0] η → MemLp η 2 μ →
      ∃ (v : Lp U 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ))
        (Y : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ)) (S : ℝ≥0 → Ω → E),
        RawSolution (𝓕:=CommonTimeShift.filtration 𝓕 a) b
          (fun i => ((hW i).shift a).toIsPreBrownianReal)
          (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) δ η A B C D
          (SwitchingFeedbackIdentity.feedback δ K S) S v Y ∧ S δ =ᵐ[μ] 0) :
    ∃ (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
      (R : ℝ≥0 → Ω → E),
      RawSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ A B C D
        (ShiftedFeedbackIdentity.feedback a δ K R) R u X ∧ R T =ᵐ[μ] 0 := by
  have ha : a ≤ T := by rw [←h]; exact le_add_right le_rfl
  obtain ⟨X₀,R₀,hp₀,hc₀,h2₀,hr₀,hi₀,hs₀,_,he₀⟩ :=
    HilbertBrownianPath.exists_full_solution b c hW hWm i₀ T A B C D ξ hξ hξ2 0
  have hη : StronglyMeasurable[(CommonTimeShift.filtration 𝓕 a) 0] (R₀ a) := by
    convert hp₀.stronglyAdapted a using 1
    simp [CommonTimeShift.filtration]
  have hη2 : MemLp (R₀ a) 2 μ := CommonProcessSpace.eval_memLp_of_s2 hp₀.stronglyAdapted T hc₀ h2₀ ha
  obtain ⟨v,Y,S,q,hST⟩ := hnull (R₀ a) hη hη2
  have hY := RawSolution.to_section b (fun i => ((hW i).shift a).toIsPreBrownianReal)
    (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) δ (R₀ a) A B C D _ S v Y q
  have hSe : ∀ t, t ≤ δ → S t =ᵐ[μ] integralState (𝓕:=CommonTimeShift.filtration 𝓕 a) b
      (fun i => ((hW i).shift a).toIsPreBrownianReal)
      (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) δ (R₀ a)
      (A.compLp Y+B.compLp v) (fun i => (C i).compLp Y+(D i).compLp v) (t:ℝ) := by
    intro t ht
    filter_upwards [q.equation t ht,primitive_ae δ t (by exact_mod_cast ht) A B
      (SwitchingFeedbackIdentity.feedback δ K S) S v Y q.control_rep q.state_rep] with ω he hd
    simpa only [integralState,Real.toNNReal_coe,hd] using he
  let u := VectorH2Extension.extendShift c (hWm i₀) a δ T h.le v
  obtain ⟨X,R,hp,hc,h2,hr,hi,hs,_,he⟩ :=
    HilbertBrownianPath.exists_full_solution b c hW hWm i₀ T A B C D ξ hξ hξ2 u
  have hpzero : restrict ha u = restrict ha (0 : Lp U 2 (spacetimeMeasure 𝓕 μ T)) := by
    change restrict ha u = (VectorH2Series.restrictCLM ha) (0 : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    rw [map_zero]
    exact VectorH2Extension.restriction_extendShift_zero c (hWm i₀) a δ T a h.le le_rfl v
  have hstart := HilbertPrefixUniqueness.at_prefix b c hW hWm i₀ ha A B C D ξ hξ hξ2
    u 0 X X₀ (R T) (R₀ T) (R a) (R₀ a) hs hs₀ (he a ha) (he₀ a ha) hpzero
  have hrestart := HilbertRestartUniqueness.restart b c hW hWm i₀ T A B C D ξ hξ hξ2
    u X (R T) hs a δ h.le (R₀ a) hη hη2 v Y (S δ) hY R S he hSe hstart
    (VectorH2Extension.shift_extendShift c (hWm i₀) a δ T h.le v)
  have hend : R T =ᵐ[μ] 0 := by
    have hh := (hrestart.2 δ le_rfl).trans hST
    rwa [h] at hh
  have hrep := ShiftedFeedbackIdentity.feedback_ae b c (hWm i₀) a δ T h K v Y X R S
    q.control_rep q.state_rep hr hrestart.1
  exact ⟨u,X,R,RawPathOfRepresentative.raw_solution b (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
    A B C D _ R u X (ShiftedFeedbackIdentity.progressive b c a δ K R hp) hrep hp hc h2 hr he,hend⟩

end LinearStochastic.HilbertFeedbackExtension
