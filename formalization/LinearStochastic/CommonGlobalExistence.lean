import LinearStochastic.CommonSolutionPaste
import LinearStochastic.CommonUniformHorizon

/-! Genuine arbitrary finite-horizon existence for controlled linear matrix
SDEs, constructed by a finite deterministic mesh on the original probability
space. Every step uses actual restarted Brownian increments and the proved
Lebesgue/Itô compatibility, with continuous S² paths throughout. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonGlobalExistence
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonLocalSolution
open CommonSolutionData CommonHorizonRestriction CommonShiftH2 CommonShiftSimple
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

include hWc

/-- Each finite mesh is constructed by genuine consecutive local solutions.
The hypothesis is only the explicit deterministic entry bound for one step. -/
theorem exists_grid (i₀ : ι) (δ : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (hb : CommonUniformHorizon.bound δ A C < 1)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) :
    ∀ N : ℕ, ∀ u : ν → H2 𝓕 μ ((N:ℝ≥0)*δ),
      Nonempty (Solution hW hWm ((N:ℝ≥0)*δ) A B C D ξ u) := by
  intro N
  induction N with
  | zero =>
    intro u
    have hc : rate (𝓕:=𝓕) (μ:=μ) (((0:ℕ):ℝ≥0)*δ) A C < 1 := by
      simp [rate]
    exact exists_local hW hWm hWc i₀ _ A B C D ξ hξ hξ2 u hc
  | succ n ih =>
    have htime : ((n+1:ℕ):ℝ≥0)*δ = (n:ℝ≥0)*δ+δ := by push_cast; ring
    rw [htime]
    intro u
    let a : ℝ≥0 := (n:ℝ≥0)*δ
    obtain ⟨q⟩ := ih (fun b ↦ restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl) (u b))
    have hstart (b : κ) := endpoint_memLp hW hWm a A B C D ξ _ q b
    have hc : rate (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ A C < 1 :=
      (CommonPicardHorizon.rate_le δ A C).trans_lt hb
    have hF0 : 𝓕 a ≤ CommonTimeShift.filtration 𝓕 a 0 := by
      change 𝓕 a ≤ 𝓕 (a+0)
      rw [add_zero]
    obtain ⟨r⟩ := exists_local (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
      (fun i ↦ CommonTimeShift.continuous_driver (hWc i) a) i₀ δ A B C D
      (fun b ↦ q.path b a) (fun b ↦ (hstart b).1.mono hF0) (fun b ↦ (hstart b).2)
      (fun b ↦ shiftCLM a δ (a+δ) le_rfl (u b)) hc
    exact CommonSolutionPaste.exists_paste hW hWm i₀ a δ A B C D ξ u q r

/-- On every finite horizon, the literal controlled system has an actual
continuous progressive S² solution with predictable H² coefficients and the
constructed integral equation at every time, including both endpoints. -/
theorem exists_global (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T) :
    Nonempty (Solution hW hWm T A B C D ξ u) := by
  obtain ⟨N,hN,hb⟩ := CommonUniformHorizon.exists_mesh T A C
  have hne : (N:ℝ≥0) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N:ℝ≥0)*(T/(N:ℝ≥0)) = T := mul_div_cancel₀ T hne
  have hh := exists_grid hW hWm hWc i₀ (T/(N:ℝ≥0)) A B C D hb ξ hξ hξ2 N
  rw [he] at hh
  exact hh u

/-- Ordinary progressive H² controls are admitted via the genuinely proved
predictable representative theorem; no predictability assumption is imposed
on the user's raw control process. -/
theorem exists_global_progressive_control (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (v : ν → ℝ≥0 → Ω → ℝ)
    (hv : ∀ b, IsProgressive 𝓕 (v b))
    (hv2 : ∀ b, MemLp (Function.uncurry (v b)) 2 ((timeMeasure_T T).prod μ)) :
    ∃ u : ν → H2 𝓕 μ T,
      (∀ b, (u b : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ] Function.uncurry (v b)) ∧
      Nonempty (Solution hW hWm T A B C D ξ u) := by
  choose u hu using fun b ↦ ProgressivePredictable.exists_predictable_Lp_of_progressive μ (hv b) T 2 (hv2 b)
  exact ⟨u,hu,exists_global hW hWm hWc i₀ T A B C D ξ hξ hξ2 u⟩
end LinearStochastic.CommonGlobalExistence
