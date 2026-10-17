module

public import LinearStochastic.HilbertLocalSolution

@[expose] public section

/-! The terminal of any genuine section solution lies in the actual F_T
square-integrable space. No endpoint integrability or measurability is assumed. -/
noncomputable section
namespace LinearStochastic.SectionTerminalSpace
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct LpOrthonormalCoordinates
open CoordinateIntegralReconstruction SectionLinearDuality LinearDuality

variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {𝓕 : Filtration ℝ≥0 mΩ}

/-- Actual vector-valued terminal Lebesgue integration, reconstructed through
the already proved scalar terminal operator. -/
def terminalDrift (T : ℝ≥0) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) : Lp E 2 μ :=
  assemble b (fun a => BSDETerminal.terminal 𝓕 T (coordinate b a f))

theorem terminalDrift_ae (T : ℝ≥0) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    terminalDrift b T f =ᵐ[μ] fun ω => ∫ s in Ioc 0 (T : ℝ), f (s.toNNReal,ω) := by
  have hprim := primitive_assemble_ae b T T le_rfl (fun a => coordinate b a f)
  rw [assemble_coordinates (mΛ:=𝓕.predictable)] at hprim
  have hc : ∀ᵐ ω ∂μ, ∀ a,
      BSDETerminal.terminal 𝓕 T (coordinate b a f) ω =
        ∫ s in Ioc 0 (T : ℝ), coordinate b a f (s.toNNReal,ω) := by
    rw [ae_all_iff]
    exact fun a => BSDETerminal.terminal_ae_real 𝓕 T _
  filter_upwards [assemble_ae b (fun a => BSDETerminal.terminal 𝓕 T (coordinate b a f)),hc,hprim]
    with ω ha hc hp
  rw [terminalDrift,ha,hp]
  exact Finset.sum_congr rfl (fun a _ => congrArg (fun q : ℝ => q • b a) (hc a))

include b in
theorem primitive_terminal_memLp (T : ℝ≥0) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    MemLp (fun ω => ∫ s in Ioc 0 (T : ℝ), f (s.toNNReal,ω)) 2 μ :=
  (memLp_congr_ae (terminalDrift_ae b T f)).mp (Lp.memLp _)

variable {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- Genuine square integrability of a separately specified terminal follows
from the actual integral equation and initial square integrability. -/
theorem SectionIntegralSolution.terminal_memLp (T : ℝ≥0) (ξ XT : Ω → E)
    (f X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT) (hξ : MemLp ξ 2 μ) :
    MemLp XT 2 μ := by
  apply (memLp_congr_ae hX.terminal).mpr
  unfold integralState
  rw [Real.toNNReal_coe]
  exact (primitive_terminal_memLp b T f).add (hξ.add (vectorProcess_memLp b hW hWm T T φ))

/-- The actual terminal belongs to F_T, using progressive drift measurability
and the constructed vector martingale's adaptedness. -/
theorem SectionIntegralSolution.terminal_aestronglyMeasurable (T : ℝ≥0) (ξ XT : Ω → E)
    (f X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT)
    (hξ : StronglyMeasurable[𝓕 0] ξ) : AEStronglyMeasurable[𝓕 T] XT μ := by
  have hp : IsStronglyPredictable 𝓕 (Function.curry f) := Lp.stronglyMeasurable f
  have hd := ProgressivePredictable.primitive_stronglyAdapted hp.isStronglyProgressive T
  have hi := (vectorProcess_martingale b hW hWm T φ).stronglyAdapted T
  have hstate : StronglyMeasurable[𝓕 T] (integralState b hW hWm T ξ f φ T) :=
    by
      unfold integralState
      rw [Real.toNNReal_coe]
      exact hd.add ((hξ.mono (𝓕.mono bot_le)).add hi)
  exact hstate.aestronglyMeasurable.congr hX.terminal.symm

end LinearStochastic.SectionTerminalSpace
