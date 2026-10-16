import LinearStochastic.BSDEHilbertCoordinates
import LinearStochastic.CoordinatePathSolution
import LinearStochastic.BSDEPathData
import LinearStochastic.SectionSolutionLinearity

/-! A genuine global coordinate adjoint solution gives the original Hilbert
adjoint equation, its actual terminal datum, and a continuous S² realization. -/
noncomputable section
namespace LinearStochastic.BSDEHilbertGlobal
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonVectorPicard LpOrthonormalCoordinates HilbertLocalSolution
open BSDEHilbertCoordinates CoordinatePathSolution SectionLinearDuality

variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- The actual coordinate solution is reconstructed in the original state
space, with the prescribed terminal variable retained independently of all
time-almost-everywhere statements. -/
theorem section_backward (T : ℝ≥0) (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E)
    (η : Lp E 2 μ)
    (q : BSDEPathData.Solution (𝓕:=𝓕) hW hWm T (coefficientMatrix b b A)
      (fun i => coefficientMatrix b b (C i)) (fun j => VectorItoProduct.coordinate b j η)) :
    ∃ (ξ : Ω → E), StronglyMeasurable[𝓕 0] ξ ∧ MemLp ξ 2 μ ∧
      ∃ (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)),
        SectionIntegralSolution b hW hWm T ξ
          (-(A.adjoint.compLp Y+∑ i, (C i).adjoint.compLp (Z i))) Z Y η ∧
        Nonempty (ContinuousRealization T ξ Y η) := by
  let ξc := fun j => q.path j 0
  let f := -BSDEMatrixPicard.driver T (coefficientMatrix b b A) (fun i => coefficientMatrix b b (C i)) q.X
  let φ := fun i j => q.X.2 j i
  have hs := CoordinatePathSolution.section_solution b hW hWm T ξc f φ q.X.1 q.path
    q.representative q.equation
  have hr := CoordinatePathSolution.continuousRealization b T ξc q.X.1 q.path
    q.representative q.continuous (fun _ => Filter.EventuallyEq.rfl)
  have ht : reconstruct b q.path T =ᵐ[μ] η := by
    have hterm : ∀ᵐ ω ∂μ, ∀ j, q.path j T ω = VectorItoProduct.coordinate b j η ω := by
      rw [ae_all_iff]; exact q.terminal
    filter_upwards [hterm,assemble_ae b (fun j => VectorItoProduct.coordinate b j η)] with ω ht ha
    rw [assemble_coordinates b η] at ha
    rw [ha]
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun r : ℝ => r • b j) (ht j))
  have hf : assemble (mΛ:=𝓕.predictable) b f =
      -(A.adjoint.compLp (assemble (mΛ:=𝓕.predictable) b q.X.1) +
        ∑ i, (C i).adjoint.compLp (assemble (mΛ:=𝓕.predictable) b (φ i))) := by
    exact (assemble_neg (mΛ:=𝓕.predictable) b _).trans
      (congrArg Neg.neg (assemble_driver b T A C q.X))
  rw [hf] at hs
  let ξ := fun ω => ∑ j, ξc j ω • b j
  have hξ : StronglyMeasurable[𝓕 0] ξ := by
    apply Finset.stronglyMeasurable_fun_sum
    intro j _
    exact ((q.progressive j).isStronglyProgressive.stronglyAdapted 0).smul_const (b j)
  have hξ2 : MemLp ξ 2 μ := by
    apply memLp_finsetSum Finset.univ
    intro j _
    exact (ContinuousLinearMap.toSpanSingleton ℝ (b j)).comp_memLp'
      (BSDEPathData.section_memLp hW hWm T _ _ _ q j 0 (bot_le)).2
  exact ⟨ξ,hξ,hξ2,assemble (mΛ:=𝓕.predictable) b q.X.1,
    (fun i => assemble (mΛ:=𝓕.predictable) b (φ i)),
    ⟨hs.sections,ht.symm.trans hs.terminal⟩,
    ⟨{hr with terminal := ht.symm.trans hr.terminal}⟩⟩

end LinearStochastic.BSDEHilbertGlobal
