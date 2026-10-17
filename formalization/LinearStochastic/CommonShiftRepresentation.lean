module

public import LinearStochastic.CommonShiftIntegral
public import LinearStochastic.BSDEIntegralRange

@[expose] public section

noncomputable section
namespace LinearStochastic.CommonShiftRepresentation
open MeasureTheory ProbabilityTheory CommonItoMultichannel CommonItoProcessGeneral CommonTimeShift
open scoped NNReal BigOperators
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t => W i t ω) (fun ω t => W j t ω) μ)

include hpair in
omit [Fintype ι] [IsProbabilityMeasure μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ] in
/-- Actual paired future-increment independence after a deterministic shift. -/
theorem pair_shift (a : ℝ≥0) (i j : ι) :
    CommonItoCross.PairForwardIndependent (driver (W i) a) (driver (W j) a)
      (filtration 𝓕 a) μ := by
  intro s
  have he : (fun ω => (fun u => driver (W i) a (s+u) ω - driver (W i) a s ω,
        fun u => driver (W j) a (s+u) ω - driver (W j) a s ω)) =
      (fun ω => (fun u => W i ((a+s)+u) ω - W i (a+s) ω,
        fun u => W j ((a+s)+u) ω - W j (a+s) ω)) := by
    funext ω
    congr 1 <;> funext u <;> simp only [driver,add_assoc] <;> ring
  change Indep (𝓕 (a+s)) (MeasurableSpace.comap _ inferInstance) μ
  rw [he]
  exact hpair i j (a+s)

include hchannels in
omit [Fintype ι] [IsProbabilityMeasure μ] in
/-- Whole-coordinate independence is preserved under actual path shifts. -/
theorem channels_shift (a : ℝ≥0) (i j : ι) (hij : i ≠ j) :
    IndepFun (fun ω t => driver (W i) a t ω) (fun ω t => driver (W j) a t ω) μ := by
  have hg : Measurable (fun f : ℝ≥0 → ℝ => fun t => f (a+t) - f a) := by fun_prop
  exact (hchannels i j hij).comp hg hg

/-- A true representation on `[0,a+δ]` gives a true representation after time
`a`, retaining the full original `𝓕_a` initial information. The integrand is the
actual predictable translation and the integral identity is proved by restart. -/
theorem represented_shift (a δ : ℝ≥0) (F : Lp ℝ 2 μ)
    (hF : BSDEIntegralRange.Represented hW hWm hpair hchannels (a+δ) F) :
    BSDEIntegralRange.Represented (𝓕 := filtration 𝓕 a)
      (fun i => preBrownian (hW i) a) (fun i => CommonShiftSimple.shiftedMeas (hWm i) a)
      (pair_shift hpair a) (channels_shift hchannels a) δ F := by
  obtain ⟨ξ,hξ,f,he⟩ := hF
  let M : Lp ℝ 2 μ := ∑ i, itoProcessCLM (hW i) (a+δ) a (hWm i) (f i)
  let η := ξ+M
  let g : BSDEIntegralRange.ChannelH2 (ι := ι) (𝓕 := filtration 𝓕 a) (μ := μ) δ :=
    WithLp.toLp 2 (fun i => CommonShiftH2.shiftCLM a δ (a+δ) le_rfl (f i))
  have hM : M ∈ lpMeas ℝ ℝ (𝓕 a) 2 μ := by
    apply Submodule.sum_mem
    intro i _
    exact itoProcessCLM_aeStronglyMeasurable (hW i) (a+δ) a (hWm i) (f i)
  have hη : AEStronglyMeasurable[filtration 𝓕 a 0] η μ := by
    change AEStronglyMeasurable[𝓕 (a+0)] η μ
    rw [add_zero]
    exact mem_lpMeas_iff_aestronglyMeasurable.mp (add_mem (hξ.mono (𝓕.mono bot_le)) hM)
  have hi : BSDEIntegralRange.integral (𝓕 := filtration 𝓕 a)
      (fun i => preBrownian (hW i) a) (fun i => CommonShiftSimple.shiftedMeas (hWm i) a)
      (pair_shift hpair a) (channels_shift hchannels a) δ g =
      BSDEIntegralRange.integral hW hWm hpair hchannels (a+δ) f - M := by
    change (∑ i, CommonItoCLM.itoIntegralCLM_T (𝓕 := filtration 𝓕 a)
      (preBrownian (hW i) a) δ (CommonShiftSimple.shiftedMeas (hWm i) a)
      (CommonShiftH2.shiftCLM a δ (a+δ) le_rfl (f i))) = _
    calc
      _ = ∑ i, (CommonItoCLM.itoIntegralCLM_T (𝓕 := 𝓕) (hW i) (a+δ) (hWm i) (f i) -
          itoProcessCLM (hW i) (a+δ) a (hWm i) (f i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact CommonShiftIntegral.integral_shift (hW i) (hWm i) a δ (f i)
      _ = _ := Finset.sum_sub_distrib _ _
  refine ⟨η,hη,g,?_⟩
  rw [hi,he]
  dsimp [η]
  abel

end LinearStochastic.CommonShiftRepresentation
