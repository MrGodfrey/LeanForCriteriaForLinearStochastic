import LinearStochastic.VectorH2Extension
import LinearStochastic.CommonDriftRestart
import LinearStochastic.SectionTerminalSpace

/-! True terminal Lebesgue integration on a zero-extended time window.
The interval-length bound is proved by restart of the actual primitive. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.TerminalDriftWindow
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonVectorPicard CommonItoCLM
open LpOrthonormalCoordinates VectorItoProduct SectionTerminalSpace
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent W 𝓕 μ] (hWm : ∀ t, Measurable (W t))

/-- Exact L² decomposition of the actual terminal drift across two adjacent
intervals, with the original random space and restarted filtration. -/
theorem terminal_restart (a δ : ℝ≥0) (f : H2 𝓕 μ (a+δ)) :
    BSDETerminal.terminal 𝓕 (a+δ) f =
      BSDETerminal.terminal 𝓕 a (CommonHorizonRestriction.restriction hWm (le_add_right le_rfl) f) +
      BSDETerminal.terminal (CommonTimeShift.filtration 𝓕 a) δ
        (CommonShiftH2.shiftCLM a δ (a+δ) le_rfl f) := by
  apply Lp.ext
  filter_upwards [BSDETerminal.terminal_ae 𝓕 (a+δ) f,
    BSDETerminal.terminal_ae 𝓕 a (CommonHorizonRestriction.restriction hWm (le_add_right le_rfl) f),
    BSDETerminal.terminal_ae (CommonTimeShift.filtration 𝓕 a) δ (CommonShiftH2.shiftCLM a δ (a+δ) le_rfl f),
    CommonDriftRestart.primitive_restart a δ (a+δ) le_rfl f,
    CommonDriftRestart.primitive_restriction hWm (le_add_right le_rfl) f,
    Lp.coeFn_add (BSDETerminal.terminal 𝓕 a (CommonHorizonRestriction.restriction hWm (le_add_right le_rfl) f))
      (BSDETerminal.terminal (CommonTimeShift.filtration 𝓕 a) δ (CommonShiftH2.shiftCLM a δ (a+δ) le_rfl f))]
    with ω ht ha hδ hr hp hs
  rw [hs,Pi.add_apply,ht,ha,hδ]
  change (∫ s in Ioc 0 (a+δ), f (s,ω) ∂CommonItoL2.timeMeasure) = _
  exact (hr δ le_rfl).trans (congrArg (fun x : ℝ ↦ x +
    ∫ s in Ioc 0 δ, CommonShiftH2.shiftCLM a δ (a+δ) le_rfl f (s,ω) ∂CommonItoL2.timeMeasure)
    (hp a le_rfl).symm)

/-- Genuine zero extension preserves the terminal drift of the local input. -/
theorem terminal_extendShift (a δ : ℝ≥0)
    (g : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) :
    BSDETerminal.terminal 𝓕 (a+δ) (CommonH2Extension.extendShift hWm a δ (a+δ) le_rfl g) =
      BSDETerminal.terminal (CommonTimeShift.filtration 𝓕 a) δ g := by
  rw [terminal_restart hWm,CommonH2Extension.restriction_extendShift_zero hWm a δ (a+δ) a le_rfl le_rfl,
    CommonH2Extension.shift_extendShift]
  change BSDETerminal.terminal 𝓕 a (0 : H2 𝓕 μ a) + _ = _
  rw [map_zero,zero_add]

section Vector
variable {E κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] (b : OrthonormalBasis κ ℝ E)

omit hWm [CompleteSpace E] in
/-- The actual vector terminal drift obeys the sharp square-root time bound. -/
theorem terminalDrift_norm (T : ℝ≥0) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    ‖terminalDrift b T f‖ ≤ Real.sqrt (T:ℝ)*‖f‖ := by
  have hs : ‖terminalDrift b T f‖^2 ≤ (T:ℝ)*‖f‖^2 := by
    rw [VectorH2Extension.norm_sq_coordinates b,VectorH2Extension.norm_sq_coordinates (mΛ:=𝓕.predictable) b,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [terminalDrift,coordinate_assemble]
    have h := BSDETerminal.terminal_norm 𝓕 T (coordinate b j f)
    have hh := pow_le_pow_left₀ (norm_nonneg _) h 2
    simpa only [mul_pow,Real.sq_sqrt T.coe_nonneg] using hh
  have he : (Real.sqrt (T:ℝ)*‖f‖)^2 = (T:ℝ)*‖f‖^2 := by rw [mul_pow,Real.sq_sqrt T.coe_nonneg]
  nlinarith [norm_nonneg (terminalDrift b T f),mul_nonneg (Real.sqrt_nonneg (T:ℝ)) (norm_nonneg f)]

omit [CompleteSpace E] in
/-- The vector primitive equality is proved coordinatewise for the actual
orthonormal lift and actual zero-extension operator. -/
theorem terminalDrift_extendShift (a δ : ℝ≥0)
    (g : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ)) :
    terminalDrift b (a+δ) (VectorH2Extension.extendShift b hWm a δ (a+δ) le_rfl g) =
      terminalDrift b δ g := by
  have hc : (fun j ↦ coordinate b j
      (terminalDrift b (a+δ) (VectorH2Extension.extendShift b hWm a δ (a+δ) le_rfl g))) =
      fun j ↦ coordinate b j (terminalDrift b δ g) := by
    funext j
    simp only [terminalDrift,coordinate_assemble,VectorH2Extension.coordinate_extendShift]
    exact terminal_extendShift hWm a δ _
  exact (assemble_coordinates b _).symm.trans ((congrArg (assemble b) hc).trans (assemble_coordinates b _))

omit [CompleteSpace E] in
/-- A window of length δ costs sqrt(δ), even on a fixed longer horizon. -/
theorem terminalDrift_window_bound (a δ : ℝ≥0)
    (g : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ)) :
    ‖terminalDrift b (a+δ) (VectorH2Extension.extendShift b hWm a δ (a+δ) le_rfl g)‖ ≤
      Real.sqrt (δ:ℝ)*‖g‖ := by
  rw [terminalDrift_extendShift]
  exact terminalDrift_norm b δ g
end Vector
end LinearStochastic.TerminalDriftWindow
