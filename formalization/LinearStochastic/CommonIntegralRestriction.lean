import LinearStochastic.CommonIntegralPaste

/-! Prefix and restart of genuine integral equations, proved from the actual
Lebesgue and Itô operators on the same probability space. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonIntegralRestriction
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonItoProcessGeneral
open CommonHorizonRestriction CommonShiftH2 CommonShiftSimple CommonIntegralPaste
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

theorem restrict_equation (i₀ : ι) (a T : ℝ≥0) (ha : a ≤ T) (ξ : Ω → ℝ)
    (g : H2 𝓕 μ T) (σ : ι → H2 𝓕 μ T) (R : ℝ≥0 → Ω → ℝ)
    (hR : IntegralEquation hW hWm T ξ g σ R) :
    IntegralEquation hW hWm a ξ (restriction (hWm i₀) ha g)
      (fun i ↦ restriction (hWm i) ha (σ i)) R := by
  intro t ht
  filter_upwards [hR t (ht.trans ha),CommonDriftRestart.primitive_restriction (hWm i₀) ha g]
    with ω he hd
  rw [he,hd t ht]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun q : Lp ℝ 2 μ ↦ q ω) (process_restriction (hW i) (hWm i) ht ha (σ i)).symm

/-- The actual process after restart solves the actual shifted equation with
its true value at time a as initial datum. -/
theorem shift_equation (a δ T : ℝ≥0) (h : a+δ ≤ T) (ξ : Ω → ℝ)
    (g : H2 𝓕 μ T) (σ : ι → H2 𝓕 μ T) (R : ℝ≥0 → Ω → ℝ)
    (hR : IntegralEquation hW hWm T ξ g σ R) :
    IntegralEquation (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
      δ (R a) (shiftCLM a δ T h g) (fun i ↦ shiftCLM a δ T h (σ i)) (fun t ↦ R (a+t)) := by
  intro t ht
  have ha : a ≤ T := (le_add_right le_rfl).trans h
  have hat : a+t ≤ T := (add_le_add le_rfl ht).trans h
  have hi : ∀ᵐ ω ∂μ, ∀ i,
      itoProcessCLM (CommonTimeShift.preBrownian (hW i) a) δ t (shiftedMeas (hWm i) a)
        (shiftCLM a δ T h (σ i)) ω = itoProcessCLM (hW i) T (a+t) (hWm i) (σ i) ω -
          itoProcessCLM (hW i) T a (hWm i) (σ i) ω := by
    rw [ae_all_iff]
    intro i
    have he := CommonRestartIntegral.process_restart (hW i) (hWm i) a δ T t h ht (σ i)
    have hh := Lp.coeFn_sub (itoProcessCLM (hW i) T (a+t) (hWm i) (σ i))
      (itoProcessCLM (hW i) T a (hWm i) (σ i))
    rw [←he] at hh
    exact hh
  filter_upwards [hR (a+t) hat,hR a ha,CommonDriftRestart.primitive_restart a δ T h g,hi]
    with ω he he0 hd hi
  rw [he,he0,hd t ht]
  simp_rw [hi,Finset.sum_sub_distrib]
  ring
end LinearStochastic.CommonIntegralRestriction
