import LinearStochastic.BSDELocal
import LinearStochastic.CommonH2Paste

/-! Genuine coordinate backward solutions, including the separate terminal
boundary and their actual global Lebesgue/Itô equations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BSDEPathData
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard BSDEMatrixPicard CommonIntegralPaste
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ : Type*} [Fintype ι] [Fintype κ]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Actual solution data. The driver is the literal AᵀY+ΣCᵢᵀZᵢ expression;
existence and martingale representation are not fields of this record. -/
structure Solution (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) where
  X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T
  path : κ → ℝ≥0 → Ω → ℝ
  progressive : ∀ b, IsProgressive 𝓕 (path b)
  continuous : ∀ b, ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ path b t ω) (Iic T)
  squareSup : ∀ b, MemLp (ContinuousDoobL2.pathSup (path b) T) 2 μ
  representative : ∀ b, (X.1 b : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ]
    Function.uncurry (path b)
  terminal : ∀ b, path b T =ᵐ[μ] η b
  equation : ∀ b, IntegralEquation hW hWm T (path b 0)
    (-driver T A C X b) (fun i ↦ X.2 b i) (path b)

variable (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

include hWc hpair hchannels in
/-- The actual local Picard solution inhabits the concrete backward solution
record once the true Itô-range representation is supplied. -/
theorem exists_local [𝓕.IsComplete μ] (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (hη : ∀ b, AEStronglyMeasurable[𝓕 T] (η b) μ)
    (hMR : ∀ χ : Lp ℝ 2 μ, AEStronglyMeasurable[𝓕 T] χ μ →
      BSDEIntegralRange.Represented hW hWm hpair hchannels T χ)
    (hc : BSDEMatrixPicard.rate T A C < 1) :
    Nonempty (Solution (𝓕:=𝓕) hW hWm T A C η) := by
  obtain ⟨X,hX,hclass,hterminal,hpredict,hcontinuous⟩ :=
    BSDELocal.exists_local_backward hW hWm hWc hpair hchannels i₀ T A C η hη hMR hc
  let R := BSDELocal.solutionPath hW hWm hpair hchannels i₀ T A C η X
  refine ⟨⟨X,R,fun b ↦ (hpredict b).isStronglyProgressive.isProgressive,?_,?_,?_,hterminal,?_⟩⟩
  · intro b
    simpa only [←NNReal.bot_eq_zero,Icc_bot] using hcontinuous b
  · intro b
    exact BSDELocal.solutionPath_S2 hW hWm hWc hpair hchannels i₀ T A C η X b
  · intro b
    exact ae_of_ae_trim 𝓕.predictable_le_prod (hclass b)
  · intro b t ht
    have hi := BSDELocal.fixedPoint_integral_identity hW hWm hWc hpair hchannels i₀ T A C η X hX b ht
    have hzero := BSDERealization.path_initial hW hWm hWc hpair hchannels i₀ T
      (η b) (driver T A C X b)
    filter_upwards [hi,hzero] with ω hi hz
    change R b 0 ω = _ at hz
    exact hi.trans (by rw [hz])

/-- Every time section of a genuine backward solution is an L² random variable
in its actual time sigma algebra, including the initial boundary. -/
theorem section_memLp (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (q : Solution (𝓕:=𝓕) hW hWm T A C η) (b : κ)
    (t : ℝ≥0) (ht : t ≤ T) :
    StronglyMeasurable[𝓕 t] (q.path b t) ∧ MemLp (q.path b t) 2 μ :=
  ⟨(q.progressive b).isStronglyProgressive.stronglyAdapted t,
    CommonProcessSpace.eval_memLp_of_s2 (q.progressive b).isStronglyProgressive.stronglyAdapted T
      (q.continuous b) (q.squareSup b) ht⟩

end LinearStochastic.BSDEPathData
