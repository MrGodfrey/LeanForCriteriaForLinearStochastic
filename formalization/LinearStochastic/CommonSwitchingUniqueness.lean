module

public import LinearStochastic.CommonClosedLoopSolution
public import LinearStochastic.SwitchingTimeMesh
public import LinearStochastic.SwitchingGain
public import LinearStochastic.CommonSolutionRestriction

@[expose] public section

/-! Actual uniqueness for the singular switching closed loop. Controls of two
solutions may differ; on each interval their proved state-feedback class
relations convert both equations to the same constant closed-loop equation. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonSwitchingUniqueness
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal BigOperators
open CommonVectorPicard CommonLocalSolution CommonSolutionData CommonClosedLoopSolution SwitchingTimeMesh
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  {κ ν ι : Type*} [Fintype κ] [Fintype ν] [Fintype ι]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
  (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
  (ξ : κ → Ω → ℝ) (u v : ν → H2 𝓕 μ T)
  (q : Solution (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D ξ u)
  (r : Solution (fun i => (hW i).toIsPreBrownianReal) hWm T A B C D ξ v)

local instance shiftedForwardFamily (a : ℝ≥0) :
    ∀ i, CommonItoIsometry.ForwardIndependent (fun t ω => W i (a+t) ω-W i a ω)
      (CommonTimeShift.filtration 𝓕 a) μ := fun _ => CommonTimeShift.forwardIndependent a

include i₀ in
/-- The two controls may differ, but their actual constant-gain relations give
the same autonomous closed-loop equation after a true deterministic restart. -/
theorem on_window (a δ : ℝ≥0) (h : a+δ ≤ T) (G : Matrix ν κ ℝ)
    (hi : ∀ b, q.path b a =ᵐ[μ] r.path b a)
    (hu : (fun b => CommonShiftH2.shiftCLM a δ T h (u b)) =
      matrixAction δ G (fun b => CommonShiftH2.shiftCLM a δ T h (q.X b)))
    (hv : (fun b => CommonShiftH2.shiftCLM a δ T h (v b)) =
      matrixAction δ G (fun b => CommonShiftH2.shiftCLM a δ T h (r.X b))) :
    ∀ᵐ ω ∂μ, ∀ b s, s ≤ δ → q.path b (a+s) ω = r.path b (a+s) ω := by
  let q₀ := CommonSolutionRestriction.shifted (fun i => (hW i).toIsPreBrownianReal) hWm
    a δ T h A B C D ξ u q
  let r₀ := CommonSolutionRestriction.shifted (fun i => (hW i).toIsPreBrownianReal) hWm
    a δ T h A B C D ξ v r
  let q₁ := closeLoop (fun i => ((hW i).shift a).toIsPreBrownianReal)
    (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) δ A B C D G _ _ q₀ hu
  let r₁ := closeLoop (fun i => ((hW i).shift a).toIsPreBrownianReal)
    (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) δ A B C D G _ _ r₀ hv
  let r₂ := CommonSolutionFixedPoint.withInitial (fun i => ((hW i).shift a).toIsPreBrownianReal)
    (fun i => CommonShiftSimple.shiftedMeas (hWm i) a)
    δ (A+B*G) (0 : Matrix κ ν ℝ) (fun i => C i+D i*G) (fun _ => 0)
    (fun b => r.path b a) (fun b => q.path b a) 0 r₁ (fun b => (hi b).symm)
  have hξ (b : κ) : StronglyMeasurable[(CommonTimeShift.filtration 𝓕 a) 0] (q.path b a) := by
    change StronglyMeasurable[𝓕 (a+0)] (q.path b a)
    convert (q.progressive b).isStronglyProgressive.stronglyAdapted a using 1
    simp only [add_zero]
  have hξ2 (b : κ) : MemLp (q.path b a) 2 μ :=
    CommonProcessSpace.eval_memLp_of_s2 (q.progressive b).isStronglyProgressive.stronglyAdapted T
      (q.continuous b) (q.squareSup b) ((le_add_right le_rfl).trans h)
  exact CommonBrownianGlobal.global_unique (fun i => (hW i).shift a)
    (fun i => CommonShiftSimple.shiftedMeas (hWm i) a) i₀ δ
    (A+B*G) (0 : Matrix κ ν ℝ) (fun i => C i+D i*G) (fun _ => 0) _ hξ hξ2 0 q₁ r₂

/-- Actual dyadic intervals lie in the containing horizon. -/
theorem inside (j : ℕ) : time T j+duration T j ≤ T := by rw [next_time]; exact time_le T _

variable (G : ℕ → Matrix ν κ ℝ)
  (hu : ∀ j, (fun b => CommonShiftH2.shiftCLM (time T j) (duration T j) T (inside T j) (u b)) =
    matrixAction (duration T j) (G j) (fun b => CommonShiftH2.shiftCLM (time T j) (duration T j) T (inside T j) (q.X b)))
  (hv : ∀ j, (fun b => CommonShiftH2.shiftCLM (time T j) (duration T j) T (inside T j) (v b)) =
    matrixAction (duration T j) (G j) (fun b => CommonShiftH2.shiftCLM (time T j) (duration T j) T (inside T j) (r.X b)))

include i₀ hu hv in
/-- Induction uses the actual local closed-loop uniqueness, not equality of the
global controls. Every mesh state is consequently the same. -/
theorem at_mesh : ∀ j b, q.path b (time T j) =ᵐ[μ] r.path b (time T j) := by
  intro j
  induction j with
  | zero =>
    intro b
    rw [time_zero]
    exact (q.initial b).trans (r.initial b).symm
  | succ j ih =>
    have he := on_window hW hWm i₀ T A B C D ξ u v q r
      (time T j) (duration T j) (inside T j) (G j) ih (hu j) (hv j)
    intro b
    have hh := he.mono (fun ω hω => hω b (duration T j) le_rfl)
    rw [next_time] at hh
    exact hh

include i₀ hu hv in
/-- Any two actual S² solutions of the singular piecewise-feedback equation
are indistinguishable on the whole closed horizon, including the terminal
limit. The controls are allowed to be different in the hypotheses. -/
theorem unique :
    ∀ᵐ ω ∂μ, ∀ b t, t ≤ T → q.path b t ω = r.path b t ω := by
  have hall : ∀ᵐ ω ∂μ, ∀ j b s, s ≤ duration T j →
      q.path b (time T j+s) ω = r.path b (time T j+s) ω := by
    rw [ae_all_iff]
    intro j
    exact on_window hW hWm i₀ T A B C D ξ u v q r
      (time T j) (duration T j) (inside T j) (G j)
      (at_mesh hW hWm i₀ T A B C D ξ u v q r G hu hv j) (hu j) (hv j)
  have hqc : ∀ᵐ ω ∂μ, ∀ b, ContinuousOn (fun t => q.path b t ω) (Iic T) := by
    rw [ae_all_iff]; exact q.continuous
  have hrc : ∀ᵐ ω ∂μ, ∀ b, ContinuousOn (fun t => r.path b t ω) (Iic T) := by
    rw [ae_all_iff]; exact r.continuous
  have hm : Tendsto (time T) atTop (nhdsWithin T (Iic T)) :=
    tendsto_nhdsWithin_iff.mpr ⟨time_tendsto T,Filter.Eventually.of_forall (time_le T)⟩
  filter_upwards [hall,hqc,hrc] with ω hh hqc hrc
  intro b t ht
  by_cases hlt : t < T
  · obtain ⟨j,hj⟩ := SwitchingGain.covers T t hlt
    have hs : t-time T j ≤ duration T j := by
      apply tsub_le_iff_right.mpr
      rw [add_comm,next_time]
      exact hj.2.le
    simpa only [add_tsub_cancel_of_le hj.1] using hh j b (t-time T j) hs
  · have htT : t = T := le_antisymm ht (le_of_not_gt hlt)
    rw [htT]
    have hqT : Tendsto (fun j => q.path b (time T j) ω) atTop (𝓝 (q.path b T ω)) :=
      (hqc b T (by change T ≤ T; exact le_rfl)).tendsto.comp hm
    have hrT : Tendsto (fun j => r.path b (time T j) ω) atTop (𝓝 (r.path b T ω)) :=
      (hrc b T (by change T ≤ T; exact le_rfl)).tendsto.comp hm
    apply tendsto_nhds_unique hqT
    apply hrT.congr'
    exact Filter.Eventually.of_forall (fun j => by simpa only [add_zero] using (hh j b 0 zero_le).symm)

end LinearStochastic.CommonSwitchingUniqueness
