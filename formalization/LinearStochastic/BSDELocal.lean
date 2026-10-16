import LinearStochastic.BSDERealization

/-! Actual local coordinate BSDE construction, conditional only on an explicit
martingale-representation statement about the already constructed Itô range.
This interface is intended to be instantiated by a separately proved MR theorem. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BSDELocal
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonItoMultichannel CommonVectorPicard BSDEIntegralRange BSDEProcessLift
open BSDEMatrixPicard BSDERealization
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ : Type*} [Fintype ι] [Fintype κ]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

theorem terminalInput_measurable (T : ℝ≥0) (η : Lp ℝ 2 μ) (f : H2 𝓕 μ T)
    (hη : AEStronglyMeasurable[𝓕 T] η μ) :
    AEStronglyMeasurable[𝓕 T] (terminalInput T η f) μ :=
  (hη.add (BSDETerminal.terminal_aestronglyMeasurable 𝓕 T f)).congr
    (Lp.coeFn_add η (BSDETerminal.terminal 𝓕 T f)).symm

/-- Actual continuous coordinate paths associated to the matrix backward iterate. -/
def solutionPath (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    κ → ℝ≥0 → Ω → ℝ :=
  fun a ↦ path hW hWm hpair hchannels i₀ T (η a) (driver T A C X a)

include hWc

/-- The actual fixed point agrees in predictable space-time with its continuous path. -/
theorem fixedPoint_path_class (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T)
    (hX : BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C η X = X) (a : κ) :
    X.1 a =ᵐ[spacetimeMeasure 𝓕 μ T]
      Function.uncurry (solutionPath hW hWm hpair hchannels i₀ T A C η X a) := by
  have he := congrArg (fun q : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T ↦ q.1 a) hX
  change stateStep hW hWm hWc hpair hchannels i₀ T (η a) (driver T A C X a) = X.1 a at he
  rw [← he]
  exact stateStep_ae_path hW hWm hWc hpair hchannels i₀ T (η a) _

/-- The diffusion in the equation is the actual second fixed-point component. -/
theorem fixedPoint_integral_identity (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T)
    (hX : BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C η X = X)
    (a : κ) {t : ℝ≥0} (ht : t ≤ T) :
    solutionPath hW hWm hpair hchannels i₀ T A C η X a t =ᵐ[μ] fun ω ↦
      μ[terminalInput T (η a) (driver T A C X a) | 𝓕 0] ω +
      (∫ s in Ioc (0 : ℝ≥0) t, (-(driver T A C X a) : H2 𝓕 μ T) (s,ω) ∂CommonItoL2.timeMeasure) +
      ∑ i, CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i) (X.2 a i) ω := by
  have hz := congrArg (fun q : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T ↦ q.2 a) hX
  change diffusionStep hW hWm hpair hchannels T (η a) (driver T A C X a) = X.2 a at hz
  have hi := path_integral_identity hW hWm hWc hpair hchannels i₀ T (η a) (driver T A C X a) ht
  rw [hz] at hi
  exact hi

/-- Conditional representation is applied to the genuine terminal input, whose
terminal measurability was proved from the actual Lebesgue integral. -/
theorem fixedPoint_terminal (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (hη : ∀ a, AEStronglyMeasurable[𝓕 T] (η a) μ)
    (hMR : ∀ χ : Lp ℝ 2 μ, AEStronglyMeasurable[𝓕 T] χ μ →
      Represented hW hWm hpair hchannels T χ)
    (X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) (a : κ) :
    solutionPath hW hWm hpair hchannels i₀ T A C η X a T =ᵐ[μ] η a :=
  path_terminal hW hWm hWc hpair hchannels i₀ T (η a) (driver T A C X a)
    (hMR _ (terminalInput_measurable T (η a) _ (hη a)))

/-- Local actual adjoint BSDE existence under a separately supplied theorem of
martingale representation. All solution and path conclusions are constructed. -/
theorem exists_local_backward (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (hη : ∀ a, AEStronglyMeasurable[𝓕 T] (η a) μ)
    (hMR : ∀ χ : Lp ℝ 2 μ, AEStronglyMeasurable[𝓕 T] χ μ →
      Represented hW hWm hpair hchannels T χ)
    (hc : BSDEMatrixPicard.rate T A C < 1) :
    ∃ X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T,
      BSDEMatrixPicard.picardMap hW hWm hWc hpair hchannels i₀ T A C η X = X ∧
      (∀ a, X.1 a =ᵐ[spacetimeMeasure 𝓕 μ T]
        Function.uncurry (solutionPath hW hWm hpair hchannels i₀ T A C η X a)) ∧
      (∀ a, solutionPath hW hWm hpair hchannels i₀ T A C η X a T =ᵐ[μ] η a) ∧
      (∀ a, IsStronglyPredictable 𝓕 (solutionPath hW hWm hpair hchannels i₀ T A C η X a)) ∧
      (∀ a, ∀ᵐ ω ∂μ, ContinuousOn
        (fun t ↦ solutionPath hW hWm hpair hchannels i₀ T A C η X a t ω) (Icc 0 T)) := by
  obtain ⟨X,hX,_⟩ := BSDEMatrixPicard.exists_unique_fixedPoint hW hWm hWc hpair hchannels i₀ T A C η hc
  exact ⟨X,hX,fixedPoint_path_class hW hWm hWc hpair hchannels i₀ T A C η X hX,
    fixedPoint_terminal hW hWm hWc hpair hchannels i₀ T A C η hη hMR X,
    fun a ↦ path_predictable hW hWm hWc hpair hchannels i₀ T _ _,
    fun a ↦ path_continuousOn hW hWm hWc hpair hchannels i₀ T _ _⟩

/-- The constructed coordinate paths have genuine S² norm on complete filtrations. -/
theorem solutionPath_S2 [𝓕.IsComplete μ] (i₀ : ι) (T : ℝ≥0) (A : Matrix κ κ ℝ)
    (C : ι → Matrix κ κ ℝ) (η : κ → Lp ℝ 2 μ)
    (X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) (a : κ) :
    MemLp (ContinuousDoobL2.pathSup (solutionPath hW hWm hpair hchannels i₀ T A C η X a) T) 2 μ :=
  path_S2 hW hWm hWc hpair hchannels i₀ T _ _

end LinearStochastic.BSDELocal
