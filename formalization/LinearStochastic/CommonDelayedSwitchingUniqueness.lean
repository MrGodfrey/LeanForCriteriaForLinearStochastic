import LinearStochastic.CommonSwitchingUniqueness

/-! Actual closed-loop uniqueness after an arbitrary deterministic waiting
interval. Prefix controls need only agree; later controls may differ. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonDelayedSwitchingUniqueness
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators
open CommonVectorPicard CommonLocalSolution CommonSolutionData SwitchingTimeMesh
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  {κ ν ι : Type*} [Fintype κ] [Fintype ν] [Fintype ι]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
  (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
  (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b)) (hξ2 : ∀ b, MemLp (ξ b) 2 μ)
  (u v : ν → H2 𝓕 μ T)
  (q : Solution (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D ξ u)
  (r : Solution (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D ξ v)

include i₀ hξ hξ2 in
theorem same_control (huv : u = v) :
    ∀ᵐ ω ∂μ, ∀ b t, t ≤ T → q.path b t ω = r.path b t ω := by
  subst v
  exact CommonBrownianGlobal.global_unique hW hWm i₀ T A B C D ξ hξ hξ2 u q r

omit hW hWm i₀ hξ hξ2 q r [𝓕.IsComplete μ] in
theorem inside (a δ : ℝ≥0) (h : a+δ = T) (j : ℕ) :
    (a+time δ j)+duration δ j ≤ T := by
  rw [add_assoc,next_time,←h]
  exact add_le_add le_rfl (time_le δ _)

variable (a δ : ℝ≥0) (h : a+δ = T)
  (G : ℕ → Matrix ν κ ℝ)
  (hu : ∀ j, (fun b => CommonShiftH2.shiftCLM (a+time δ j) (duration δ j) T (inside T a δ h j) (u b)) =
    matrixAction (duration δ j) (G j) (fun b => CommonShiftH2.shiftCLM (a+time δ j) (duration δ j) T (inside T a δ h j) (q.X b)))
  (hv : ∀ j, (fun b => CommonShiftH2.shiftCLM (a+time δ j) (duration δ j) T (inside T a δ h j) (v b)) =
    matrixAction (duration δ j) (G j) (fun b => CommonShiftH2.shiftCLM (a+time δ j) (duration δ j) T (inside T a δ h j) (r.X b)))

include i₀ hu hv in
theorem at_mesh (hi : ∀ b, q.path b a =ᵐ[μ] r.path b a) :
    ∀ j b, q.path b (a+time δ j) =ᵐ[μ] r.path b (a+time δ j) := by
  intro j
  induction j with
  | zero => simpa only [time_zero,add_zero] using hi
  | succ j ih =>
    have he := CommonSwitchingUniqueness.on_window hW hWm i₀ T A B C D ξ u v q r
      (a+time δ j) (duration δ j) (inside T a δ h j) (G j) ih (hu j) (hv j)
    intro b
    have hh := he.mono (fun ω hω => hω b (duration δ j) le_rfl)
    rw [add_assoc,next_time] at hh
    exact hh

include i₀ hξ hξ2 hu hv in
/-- Genuine prefix restriction and dyadic closed-loop uniqueness, joined at the
actual waiting endpoint and at the continuous final endpoint. -/
theorem unique
    (hp : (fun b => CommonHorizonRestriction.restriction (hWm i₀)
      (show a ≤ T from h ▸ le_add_right le_rfl) (u b)) =
      fun b => CommonHorizonRestriction.restriction (hWm i₀)
      (show a ≤ T from h ▸ le_add_right le_rfl) (v b)) :
    ∀ᵐ ω ∂μ, ∀ b t, t ≤ T → q.path b t ω = r.path b t ω := by
  have ha : a ≤ T := h ▸ le_add_right le_rfl
  let qp := CommonSolutionRestriction.prefixSolution (fun i => (hW i).toIsPreBrownianReal) hWm i₀ a T ha A B C D ξ u q
  let rp := CommonSolutionRestriction.prefixSolution (fun i => (hW i).toIsPreBrownianReal) hWm i₀ a T ha A B C D ξ v r
  have hprefix := same_control hW hWm i₀ a A B C D ξ hξ hξ2 _ _ qp rp hp
  have hi b : q.path b a =ᵐ[μ] r.path b a := hprefix.mono (fun ω hω => hω b a le_rfl)
  have hall : ∀ᵐ ω ∂μ, ∀ j b s, s ≤ duration δ j →
      q.path b (a+time δ j+s) ω = r.path b (a+time δ j+s) ω := by
    rw [ae_all_iff]
    intro j
    exact CommonSwitchingUniqueness.on_window hW hWm i₀ T A B C D ξ u v q r
      (a+time δ j) (duration δ j) (inside T a δ h j) (G j)
      (at_mesh hW hWm i₀ T A B C D ξ u v q r a δ h G hu hv hi j) (hu j) (hv j)
  have hqc : ∀ᵐ ω ∂μ, ∀ b, ContinuousOn (fun t => q.path b t ω) (Iic T) := by
    rw [ae_all_iff]; exact q.continuous
  have hrc : ∀ᵐ ω ∂μ, ∀ b, ContinuousOn (fun t => r.path b t ω) (Iic T) := by
    rw [ae_all_iff]; exact r.continuous
  have hm : Tendsto (fun j => a+time δ j) atTop (nhdsWithin T (Iic T)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,Eventually.of_forall (fun j => ?_)⟩
    · simpa only [h] using (tendsto_const_nhds (x:=a)).add (time_tendsto δ)
    · change a+time δ j ≤ T
      rw [←h]
      exact add_le_add le_rfl (time_le δ j)
  filter_upwards [hprefix,hall,hqc,hrc] with ω hp hh hqc hrc
  intro b t ht
  by_cases hta : t ≤ a
  · exact hp b t hta
  have hat : a ≤ t := (lt_of_not_ge hta).le
  by_cases hlt : t < T
  · have htd : t-a < δ := (tsub_lt_iff_right hat).mpr (by simpa only [h,add_comm] using hlt)
    obtain ⟨j,hj⟩ := SwitchingGain.covers δ (t-a) htd
    have hs : t-a-time δ j ≤ duration δ j := by
      apply tsub_le_iff_right.mpr
      rw [add_comm,next_time]
      exact hj.2.le
    have he := hh j b (t-a-time δ j) hs
    simpa only [add_assoc,add_tsub_cancel_of_le hj.1,add_tsub_cancel_of_le hat] using he
  · have htT : t = T := le_antisymm ht (le_of_not_gt hlt)
    rw [htT]
    have hqT := (hqc b T (by change T ≤ T; exact le_rfl)).tendsto.comp hm
    have hrT := (hrc b T (by change T ≤ T; exact le_rfl)).tendsto.comp hm
    apply tendsto_nhds_unique hqT
    apply hrT.congr'
    exact Eventually.of_forall (fun j => by simpa only [Function.comp_apply,add_zero] using (hh j b 0 zero_le).symm)

end LinearStochastic.CommonDelayedSwitchingUniqueness
