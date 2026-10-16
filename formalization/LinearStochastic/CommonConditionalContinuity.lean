import LinearStochastic.BSDEIntegralRange

noncomputable section
namespace LinearStochastic.CommonConditionalContinuity
open MeasureTheory ProbabilityTheory CommonItoMultichannel
open scoped NNReal BigOperators
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t => W i t ω) (fun ω t => W j t ω) μ)

/-- Conditional L² projection, retaining the original ambient L² space. -/
def conditional (F : Lp ℝ 2 μ) (t : ℝ≥0) : Lp ℝ 2 μ :=
  condExpL2 ℝ ℝ (𝓕.le t) F

theorem conditional_of_measurable (F : Lp ℝ 2 μ) (t : ℝ≥0)
    (hF : AEStronglyMeasurable[𝓕 t] F μ) : conditional (𝓕 := 𝓕) F t = F := by
  apply Lp.ext
  have he := (Lp.memLp F).condExpL2_ae_eq_condExp (𝕜 := ℝ) (𝓕.le t)
  rw [Lp.toLp_coeFn] at he
  exact he.trans (condExp_of_aestronglyMeasurable' (𝓕.le t) hF ((Lp.memLp F).integrable one_le_two))

/-- A true initial-plus-Ito decomposition makes the actual conditional
expectation process continuous in L², for every nonnegative time. -/
theorem continuous_conditional_of_represented (T : ℝ≥0) (F : Lp ℝ 2 μ)
    (hF : BSDEIntegralRange.Represented hW hWm hpair hchannels T F) :
    Continuous (conditional (𝓕 := 𝓕) F) := by
  obtain ⟨ξ,hξ,f,he⟩ := hF
  have hc (t : ℝ≥0) : conditional (𝓕 := 𝓕) F t = ξ +
      ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i) (f i) := by
    rw [he]
    change ((condExpL2 ℝ ℝ (𝓕.le t)) (ξ + sumIntegral hW hWm T (fun i => f i)) : Lp ℝ 2 μ) = _
    simp only [map_add,Submodule.coe_add,sumIntegral,map_sum,Submodule.coe_sum]
    have hξt := conditional_of_measurable ξ t (hξ.mono (𝓕.mono bot_le))
    change (condExpL2 ℝ ℝ (𝓕.le t) ξ : Lp ℝ 2 μ) = ξ at hξt
    rw [hξt]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact (CommonItoProcessGeneral.itoProcessCLM_eq_condExpL2 (𝓕 := 𝓕) (hW i) T t (hWm i) (f i)).symm
  have heq : conditional (𝓕 := 𝓕) F = fun t => ξ +
      ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i) (f i) := funext hc
  rw [heq]
  apply continuous_const.add
  exact continuous_finsetSum _ (fun i _ =>
    CommonItoProcessGeneral.itoIntegralProcessGen_l2_continuous (𝓕 := 𝓕) (hW i) T (hWm i) (f i))

end LinearStochastic.CommonConditionalContinuity
