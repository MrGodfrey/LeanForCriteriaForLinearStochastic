import LinearStochastic.CommonDriftRestart
import LinearStochastic.CommonProcessPaste

/-! A genuine pasting theorem for the actual Lebesgue and constructed Itô
operators. Equations use fixed-time almost-everywhere identities; no illegal
exchange of uncountably many null sets is made. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonIntegralPaste
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonItoProcessGeneral
open CommonHorizonRestriction CommonShiftH2 CommonShiftSimple
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Actual coordinate integral equation, including separate initial and terminal
times rather than only a space-time class identity. -/
def IntegralEquation (T : ℝ≥0) (ξ : Ω → ℝ) (g : H2 𝓕 μ T)
    (σ : ι → H2 𝓕 μ T) (R : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ t, t ≤ T → R t =ᵐ[μ] fun ω ↦ ξ ω +
    (∫ s in Ioc (0 : ℝ≥0) t, g (s,ω) ∂timeMeasure) +
    ∑ i, itoProcessCLM (hW i) T t (hWm i) (σ i) ω

/-- Two genuine integral equations on adjacent time intervals combine into the
same constructed global integral equation. The translation of Itô operators
is proved by simple-process density in CommonRestartIntegral. -/
theorem paste_equation (i₀ : ι) (a δ : ℝ≥0) (ξ : Ω → ℝ)
    (g : H2 𝓕 μ (a+δ)) (σ : ι → H2 𝓕 μ (a+δ))
    (R S : ℝ≥0 → Ω → ℝ)
    (hR : IntegralEquation hW hWm a ξ
      (restriction (hWm i₀) (le_add_right le_rfl) g)
      (fun i ↦ restriction (hWm i) (le_add_right le_rfl) (σ i)) R)
    (hS : IntegralEquation (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i ↦ CommonTimeShift.preBrownian (hW i) a)
      (fun i ↦ shiftedMeas (hWm i) a) δ (R a)
      (shiftCLM a δ (a+δ) le_rfl g)
      (fun i ↦ shiftCLM a δ (a+δ) le_rfl (σ i)) S) :
    IntegralEquation hW hWm (a+δ) ξ g σ (CommonProcessPaste.paste a R S) := by
  intro t ht
  by_cases hta : t ≤ a
  · have hh := hR t hta
    have hd := CommonDriftRestart.primitive_restriction (hWm i₀)
      (show a ≤ a+δ from le_add_right le_rfl) g
    filter_upwards [hh,hd] with ω hω hd
    simp only [CommonProcessPaste.paste,if_pos hta]
    rw [hω,hd t hta]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun q : Lp ℝ 2 μ ↦ q ω)
      (process_restriction (hW i) (hWm i) hta (le_add_right le_rfl) (σ i))
  · have hat : a ≤ t := le_of_not_ge hta
    have hs : t-a ≤ δ := tsub_le_iff_right.mpr (by simpa only [add_comm δ a] using ht)
    have hsum : a+(t-a) = t := add_tsub_cancel_of_le hat
    have hhS := hS (t-a) hs
    have hhR := hR a le_rfl
    have hdr := CommonDriftRestart.primitive_restriction (hWm i₀)
      (show a ≤ a+δ from le_add_right le_rfl) g
    have hds := CommonDriftRestart.primitive_restart a δ (a+δ) le_rfl g
    have hito : ∀ᵐ ω ∂μ, ∀ i,
        itoProcessCLM (CommonTimeShift.preBrownian (hW i) a) δ (t-a) (shiftedMeas (hWm i) a)
          (shiftCLM a δ (a+δ) le_rfl (σ i)) ω =
        itoProcessCLM (hW i) (a+δ) t (hWm i) (σ i) ω -
          itoProcessCLM (hW i) (a+δ) a (hWm i) (σ i) ω := by
      rw [ae_all_iff]
      intro i
      have he := CommonRestartIntegral.process_restart (hW i) (hWm i) a δ (a+δ) (t-a) le_rfl hs (σ i)
      rw [hsum] at he
      have hh := Lp.coeFn_sub (itoProcessCLM (hW i) (a+δ) t (hWm i) (σ i))
        (itoProcessCLM (hW i) (a+δ) a (hWm i) (σ i))
      rw [←he] at hh
      exact hh
    filter_upwards [hhS,hhR,hdr,hds,hito] with ω hsω hrω hdr hds hi
    simp only [CommonProcessPaste.paste,if_neg hta]
    rw [hsω,hrω,hdr a le_rfl]
    have hb : (∑ i, itoProcessCLM (hW i) a a (hWm i)
        (restriction (hWm i) (le_add_right le_rfl) (σ i)) ω) =
        ∑ i, itoProcessCLM (hW i) (a+δ) a (hWm i) (σ i) ω := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun q : Lp ℝ 2 μ ↦ q ω)
        (process_restriction (hW i) (hWm i) le_rfl (le_add_right le_rfl) (σ i))
    rw [hb]
    have hd := hds (t-a) hs
    rw [hsum] at hd
    rw [hd]
    simp_rw [hi,Finset.sum_sub_distrib]
    ring
end LinearStochastic.CommonIntegralPaste
