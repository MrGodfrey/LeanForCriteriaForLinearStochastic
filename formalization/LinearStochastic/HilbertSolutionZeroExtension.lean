module

public import LinearStochastic.CommonSolutionZeroExtension
public import LinearStochastic.CommonSmallTimeBound
public import LinearStochastic.HilbertEndpointBound
public import LinearStochastic.HilbertGlobalSolution
public import LinearStochastic.SectionSolutionLinearity

@[expose] public section

/-! Actual additive vector equations on a terminal time window.  The solution
is constructed locally and its genuine state class is extended isometrically. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.HilbertSolutionZeroExtension
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonVectorPicard CommonLocalSolution CommonSolutionData
open SectionSolutionLinearity HilbertLocalSolution LpOrthonormalCoordinates VectorItoProduct CoordinatePathSolution SectionLinearDuality
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
local instance shiftedForwardFamily (a : ℝ≥0) :
    ∀ i, CommonItoIsometry.ForwardIndependent (CommonTimeShift.driver (W i) a) (CommonTimeShift.filtration 𝓕 a) μ :=
  fun _ ↦ CommonTimeShift.forwardIndependent a

include c hWc in
/-- Local genuine existence, exact zero extension, and the actual Picard
estimate give a terminal-window solution with a vanishing state bound. -/
theorem exists_additive (i₀ : ι) (a δ : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (u : Lp U 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ))
    (hδ : (δ:ℝ)*CommonPicardHorizon.matrixSize (coefficientMatrix b b A) < 1) :
    ∃ (Y : Lp E 2 (spacetimeMeasure 𝓕 μ (a+δ))) (η : lpMeas E ℝ (𝓕 (a+δ)) 2 μ),
      SectionIntegralSolution b hW hWm (a+δ) 0
        (A.compLp Y+B.compLp (VectorH2Extension.extendShift c (hWm i₀) a δ (a+δ) le_rfl u))
        (fun i ↦ (D i).compLp (VectorH2Extension.extendShift c (hWm i₀) a δ (a+δ) le_rfl u))
        Y (η : Lp E 2 μ) ∧
      ‖Y‖ ≤ (Fintype.card κ : ℝ)*CommonSmallTimeBound.additiveFactor δ
        (coefficientMatrix b b A) (coefficientMatrix b c B) (fun i ↦ coefficientMatrix b c (D i))*‖u‖ := by
  let α := coefficientMatrix b b A
  let β := coefficientMatrix b c B
  let d := fun i ↦ coefficientMatrix b c (D i)
  let v := fun j ↦ coordinate c j u
  obtain ⟨q⟩ := CommonGlobalExistence.exists_global
    (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ CommonShiftSimple.shiftedMeas (hWm i) a)
    (fun i ↦ CommonTimeShift.continuous_driver (hWc i) a) i₀ δ α β (fun _ ↦ 0) d 0
    (fun _ ↦ stronglyMeasurable_zero) (fun _ ↦ MemLp.zero) v
  let qg := CommonSolutionZeroExtension.extend hW hWm i₀ a δ α β (fun _ ↦ 0) d v q
  let vg := fun j ↦ CommonH2Extension.extendShift (𝓕:=𝓕) (μ:=μ) (hWm i₀) a δ (a+δ) le_rfl (v j)
  let Y := assemble (mΛ:=𝓕.predictable) b qg.X
  let ug := VectorH2Extension.extendShift c (hWm i₀) a δ (a+δ) le_rfl u
  have hv : assemble (mΛ:=𝓕.predictable) c vg = ug := rfl
  have hz : (fun i : ι ↦ coefficientMatrix b b (0 : E →L[ℝ] E)) = (fun _ ↦ 0) := by
    funext i j k
    simp only [coefficientMatrix,zero_apply,inner_zero_right,Matrix.zero_apply]
  have hs := section_solution b hW hWm (a+δ) 0
    (driftInput (a+δ) α β vg qg.X) (noiseInput (a+δ) (fun _ ↦ 0) d vg qg.X)
    qg.X qg.path qg.representative qg.equation
  have hi : (fun ω ↦ ∑ j : κ, (0 : κ → Ω → ℝ) j ω • b j) = 0 := by
    funext ω
    simp
  have hf : assemble (mΛ:=𝓕.predictable) b (driftInput (a+δ) α β vg qg.X) = A.compLp Y+B.compLp ug := by
    have hh := assemble_driftInput b c (a+δ) A B vg qg.X
    simpa only [hv] using hh
  have hφ : (fun i ↦ assemble (mΛ:=𝓕.predictable) b (noiseInput (a+δ) (fun _ ↦ 0) d vg qg.X i)) =
      fun i ↦ (D i).compLp ug := by
    funext i
    have hh := assemble_noiseInput b c (a+δ) (fun _ : ι ↦ (0 : E →L[ℝ] E)) D vg qg.X i
    simp only [hz,hv] at hh
    rw [hh]
    have h0 : (0 : E →L[ℝ] E).compLp Y = 0 := by
      apply Lp.ext
      filter_upwards [(0 : E →L[ℝ] E).coeFn_compLp Y,Lp.coeFn_zero E 2 (spacetimeMeasure 𝓕 μ (a+δ))] with z h1 h2
      simpa only [zero_apply,Pi.zero_apply] using h1.trans h2.symm
    exact (congrArg (fun Z ↦ Z+(D i).compLp ug) h0).trans (zero_add _)
  rw [hi,hf,hφ] at hs
  have hη2 := SectionTerminalSpace.SectionIntegralSolution.terminal_memLp b hW hWm (a+δ) 0
    (reconstruct b qg.path (a+δ)) (A.compLp Y+B.compLp ug) Y (fun i ↦ (D i).compLp ug) hs MemLp.zero
  let η := hη2.toLp (reconstruct b qg.path (a+δ))
  have hη := SectionIntegralSolution.terminal_congr b hW hWm (a+δ) 0
    (reconstruct b qg.path (a+δ)) η (A.compLp Y+B.compLp ug) Y (fun i ↦ (D i).compLp ug) hs hη2.coeFn_toLp
  have hm := SectionTerminalSpace.SectionIntegralSolution.terminal_aestronglyMeasurable b hW hWm (a+δ)
    0 η (A.compLp Y+B.compLp ug) Y (fun i ↦ (D i).compLp ug) hη stronglyMeasurable_zero
  refine ⟨Y,⟨η,hm⟩,hη,?_⟩
  have hnorm : ‖qg.X‖ = ‖q.X‖ := CommonSolutionZeroExtension.extend_state_norm hW hWm i₀ a δ α β (fun _ ↦ 0) d v q
  have hstate := CommonSmallTimeBound.additive_state_bound
    (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ CommonShiftSimple.shiftedMeas (hWm i) a)
    (fun i ↦ CommonTimeShift.continuous_driver (hWc i) a) i₀ δ α β d v q hδ
  have hc : (fun j ↦ coordinate b j Y) = qg.X := by funext j; exact coordinate_assemble (mΛ:=𝓕.predictable) _ _ _
  have hy := HilbertEndpointBound.norm_le_card_coordinates (mΛ:=𝓕.predictable) b Y
  rw [hc,hnorm] at hy
  have hf0 : 0 ≤ CommonSmallTimeBound.additiveFactor δ α β d :=
    div_nonneg (CommonForwardBounds.inputBound_nonneg δ β d) (sub_pos.mpr hδ).le
  have hu := HilbertEndpointBound.coordinates_norm_le (mΛ:=(CommonTimeShift.filtration 𝓕 a).predictable) c u
  have hlast := hstate.trans (mul_le_mul_of_nonneg_left hu hf0)
  exact hy.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlast (Nat.cast_nonneg (Fintype.card κ)))
end LinearStochastic.HilbertSolutionZeroExtension
