import LinearStochastic.CommonSolutionRestriction
import LinearStochastic.CommonUniformHorizon

/-! Genuine arbitrary-horizon pathwise uniqueness. The proof restricts and
restarts arbitrary actual solutions, derives local Picard equations, and uses
a finite mesh whose strict contraction bound is independent of filtration. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonGlobalUniqueness
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonLocalSolution
open CommonSolutionData CommonHorizonRestriction CommonShiftH2 CommonShiftSimple
open CommonSolutionRestriction CommonSolutionFixedPoint
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

include hWc

theorem unique_grid (i₀ : ι) (δ : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (hb : CommonUniformHorizon.bound δ A C < 1)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) :
    ∀ N : ℕ, ∀ u : ν → H2 𝓕 μ ((N:ℝ≥0)*δ),
      ∀ q r : Solution hW hWm ((N:ℝ≥0)*δ) A B C D ξ u,
        ∀ᵐ ω ∂μ, ∀ b t, t ≤ (N:ℝ≥0)*δ → q.path b t ω = r.path b t ω := by
  intro N
  induction N with
  | zero =>
    intro u q r
    apply local_unique hW hWm hWc i₀ _ A B C D ξ hξ hξ2 u q r
    simp [rate]
  | succ n ih =>
    have htime : ((n+1:ℕ):ℝ≥0)*δ = (n:ℝ≥0)*δ+δ := by push_cast; ring
    rw [htime]
    intro u q r
    let a : ℝ≥0 := (n:ℝ≥0)*δ
    have ha : a ≤ a+δ := le_add_right le_rfl
    let qp := prefixSolution hW hWm i₀ a (a+δ) ha A B C D ξ u q
    let rp := prefixSolution hW hWm i₀ a (a+δ) ha A B C D ξ u r
    have hpast := ih (fun b ↦ restriction (hWm i₀) ha (u b)) qp rp
    change ∀ᵐ ω ∂μ, ∀ b t, t ≤ a → q.path b t ω = r.path b t ω at hpast
    let qs := shifted hW hWm a δ (a+δ) le_rfl A B C D ξ u q
    let rs := shifted hW hWm a δ (a+δ) le_rfl A B C D ξ u r
    have hinit (b : κ) : r.path b a =ᵐ[μ] q.path b a :=
      hpast.mono (fun ω hω ↦ (hω b a le_rfl).symm)
    let rs' := withInitial (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
      δ A B C D (fun b ↦ r.path b a) (fun b ↦ q.path b a)
      (fun b ↦ shiftCLM a δ (a+δ) le_rfl (u b)) rs hinit
    have hF0 : 𝓕 a ≤ CommonTimeShift.filtration 𝓕 a 0 := by
      change 𝓕 a ≤ 𝓕 (a+0)
      rw [add_zero]
    have hstart (b : κ) : StronglyMeasurable[CommonTimeShift.filtration 𝓕 a 0] (q.path b a) :=
      ((q.progressive b).isStronglyProgressive.stronglyAdapted a).mono hF0
    have hstart2 (b : κ) : MemLp (q.path b a) 2 μ :=
      CommonProcessSpace.eval_memLp_of_s2 (q.progressive b).isStronglyProgressive.stronglyAdapted
        (a+δ) (q.continuous b) (q.squareSup b) ha
    have hc : rate (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ A C < 1 :=
      (CommonPicardHorizon.rate_le δ A C).trans_lt hb
    have hfuture := local_unique (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
      (fun i ↦ CommonTimeShift.continuous_driver (hWc i) a) i₀ δ A B C D
      (fun b ↦ q.path b a) hstart hstart2 (fun b ↦ shiftCLM a δ (a+δ) le_rfl (u b)) qs rs' hc
    change ∀ᵐ ω ∂μ, ∀ b s, s ≤ δ → q.path b (a+s) ω = r.path b (a+s) ω at hfuture
    filter_upwards [hpast,hfuture] with ω hp hf
    intro b t ht
    by_cases hta : t ≤ a
    · exact hp b t hta
    · have hat : a ≤ t := le_of_not_ge hta
      have hs : t-a ≤ δ := tsub_le_iff_right.mpr (by simpa only [add_comm δ a] using ht)
      simpa only [add_tsub_cancel_of_le hat] using hf b (t-a) hs

/-- Two arbitrary genuine continuous S² integral solutions with the same
initial variable and actual control coincide on one probability-one set at
every time of every finite horizon. No fixed-point or global uniqueness
assumption is an input. -/
theorem global_unique (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T)
    (q r : Solution hW hWm T A B C D ξ u) :
    ∀ᵐ ω ∂μ, ∀ b t, t ≤ T → q.path b t ω = r.path b t ω := by
  obtain ⟨N,hN,hb⟩ := CommonUniformHorizon.exists_mesh T A C
  have hne : (N:ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N:ℝ≥0)*(T/(N:ℝ≥0)) = T := mul_div_cancel₀ T hne
  have hh := unique_grid hW hWm hWc i₀ (T/(N:ℝ≥0)) A B C D hb ξ hξ hξ2 N
  rw [he] at hh
  exact hh u q r
end LinearStochastic.CommonGlobalUniqueness
