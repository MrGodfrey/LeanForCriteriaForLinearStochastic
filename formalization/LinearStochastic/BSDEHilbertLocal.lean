import LinearStochastic.BSDEHilbertCoordinates

/-! Genuine local Hilbert-valued adjoint BSDE solutions. The sole probabilistic
existence premise left visible is representation in the actual Itô range. -/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BSDEHilbertLocal
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel CommonVectorPicard LpOrthonormalCoordinates HilbertLocalSolution
open BSDEMatrixPicard BSDEIntegralRange BSDEProcessLift BSDEHilbertCoordinates
open CoordinateIntegralReconstruction CoordinateSectionSolution SectionLinearDuality

variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

include hWc in
/-- Every actual F_T-measurable vector terminal datum has a genuine local
adjoint solution when scalar martingale representation is supplied. The drift,
diffusions, initial L² value and continuous realization are all constructed. -/
theorem exists_section_backward (i₀ : ι) (T : ℝ≥0) (A : E →L[ℝ] E) (C : ι → E →L[ℝ] E)
    (η : Lp E 2 μ) (hη : AEStronglyMeasurable[𝓕 T] η μ)
    (hMR : ∀ χ : Lp ℝ 2 μ, AEStronglyMeasurable[𝓕 T] χ μ →
      Represented hW hWm hpair hchannels T χ)
    (hc : BSDEMatrixPicard.rate T (coefficientMatrix b b A)
      (fun i => coefficientMatrix b b (C i)) < 1) :
    ∃ (ξ : Ω → E), StronglyMeasurable[𝓕 0] ξ ∧ MemLp ξ 2 μ ∧
      ∃ (Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (Z : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)),
        SectionIntegralSolution b hW hWm T ξ
          (-(A.adjoint.compLp Y + ∑ i, (C i).adjoint.compLp (Z i))) Z Y η ∧
        Nonempty (ContinuousRealization T ξ Y η) := by
  let a := coefficientMatrix b b A
  let γ := fun i => coefficientMatrix b b (C i)
  let ηc := fun j => VectorItoProduct.coordinate b j η
  have hηc (j : κ) : AEStronglyMeasurable[𝓕 T] (ηc j) μ :=
    ((innerSL ℝ (b j)).continuous.comp_aestronglyMeasurable hη).congr
      (VectorItoProduct.coordinate_ae b j η).symm
  obtain ⟨Q,hQ,hclass,hterm,_,_⟩ := BSDELocal.exists_local_backward hW hWm hWc hpair hchannels
    i₀ T a γ ηc hηc hMR hc
  let f := driver T a γ Q
  let ξc := fun j => μ[terminalInput T (ηc j) (f j) | 𝓕 0]
  let φ := fun i j => Q.2 j i
  have hz (j : κ) : diffusionStep hW hWm hpair hchannels T (ηc j) (f j) = Q.2 j :=
    congrArg (fun q : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) T => q.2 j) hQ
  have hrep (j : κ) : Q.1 j =ᵐ[spacetimeMeasure 𝓕 μ T]
      Function.uncurry (CommonPicardRealization.realization hWm i₀ T (ξc j) (-f j) (fun i => φ i j)) := by
    have hr := hclass j
    change Q.1 j =ᵐ[spacetimeMeasure 𝓕 μ T]
      Function.uncurry (CommonPicardRealization.realization hWm i₀ T (ξc j) (-f j)
        (fun i => diffusionStep hW hWm hpair hchannels T (ηc j) (f j) i)) at hr
    rw [hz j] at hr
    exact hr
  have hs := section_solution b hW hWm hWc i₀ T ξc (-f) φ Q.1 hrep
  have hr := continuousRealization b hW hWm hWc i₀ T ξc (-f) φ Q.1 hrep
  have ht : state b hWm i₀ T ξc (-f) φ T =ᵐ[μ] η := by
    have hpoint : ∀ᵐ ω ∂μ, ∀ j, BSDELocal.solutionPath hW hWm hpair hchannels
        i₀ T a γ ηc Q j T ω = ηc j ω := by
      rw [ae_all_iff]
      exact hterm
    filter_upwards [hpoint,assemble_ae b ηc] with ω hp ha
    rw [assemble_coordinates b η] at ha
    rw [ha]
    apply Finset.sum_congr rfl
    intro j _
    apply congrArg (fun q : ℝ => q • b j)
    have he := hp j
    change CommonPicardRealization.realization hWm i₀ T (ξc j) (-f j)
      (fun i => diffusionStep hW hWm hpair hchannels T (ηc j) (f j) i) T ω = ηc j ω at he
    rw [hz j] at he
    exact he
  have hf : assemble (mΛ:=𝓕.predictable) b (-f) =
      -(A.adjoint.compLp (assemble (mΛ:=𝓕.predictable) b Q.1) +
        ∑ i, (C i).adjoint.compLp (assemble (mΛ:=𝓕.predictable) b (φ i))) := by
    rw [assemble_neg (mΛ:=𝓕.predictable),show f = driver T (coefficientMatrix b b A)
      (fun i => coefficientMatrix b b (C i)) Q from rfl,assemble_driver]
  rw [hf] at hs
  let ξ := fun ω => ∑ j, ξc j ω • b j
  have hξ : StronglyMeasurable[𝓕 0] ξ := by
    apply Finset.stronglyMeasurable_fun_sum
    intro j _
    exact stronglyMeasurable_condExp.smul_const (b j)
  have hξ2 : MemLp ξ 2 μ := by
    apply memLp_finsetSum Finset.univ
    intro j _
    exact (ContinuousLinearMap.toSpanSingleton ℝ (b j)).comp_memLp'
      ((Lp.memLp (terminalInput T (ηc j) (f j))).condExp one_le_two)
  refine ⟨ξ,hξ,hξ2,assemble (mΛ:=𝓕.predictable) b Q.1,
    (fun i => assemble (mΛ:=𝓕.predictable) b (φ i)),?_,?_⟩
  · exact ⟨hs.sections,ht.symm.trans hs.terminal⟩
  · exact ⟨{ hr with terminal := ht.symm.trans hr.terminal }⟩

#print axioms exists_section_backward
end LinearStochastic.BSDEHilbertLocal
