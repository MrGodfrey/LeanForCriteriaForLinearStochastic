import LinearStochastic.SwitchingNullSmall
import LinearStochastic.HilbertNullExtension

/-! Exact null control at every positive horizon for the actual original SDE.
For long horizons the real control is zero until the final unit interval. -/
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.SwitchingNullAll
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
open CommonItoMultichannel SectionLinearDuality
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n r m : ℕ} [Nonempty (Fin n)]
  {W : Fin m → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (i₀ : Fin m)
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)
  (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
  (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)

local instance shiftedForwardFamily (a : ℝ≥0) :
    ∀ i, CommonItoIsometry.ForwardIndependent (fun t ω => W i (a+t) ω-W i a ω)
      (CommonTimeShift.filtration 𝓕 a) μ := fun _ => CommonTimeShift.forwardIndependent a

include i₀ hpair hchannels in
theorem exists_null (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥)
    (ξ : Ω → EuclideanSpace ℝ (Fin n)) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ) :
    ∃ (u : Lp (EuclideanSpace ℝ (Fin r)) 2 (spacetimeMeasure 𝓕 μ T))
      (X : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T)),
      SectionIntegralSolution (EuclideanSpace.basisFun (Fin n) ℝ)
        (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
        (A.toEuclideanLin.toContinuousLinearMap.compLp X+B.toEuclideanLin.toContinuousLinearMap.compLp u)
        (fun i => (C i).toEuclideanLin.toContinuousLinearMap.compLp X+(D i).toEuclideanLin.toContinuousLinearMap.compLp u)
        X (0 : Ω → EuclideanSpace ℝ (Fin n)) := by
  by_cases hT1 : T ≤ 1
  · obtain ⟨c₀,N,hc,hN,hh⟩ := SwitchingNullSmall.uniform_cost hW hWm i₀ hpair hchannels A B C D hm hflag
    obtain ⟨u,X,hX,_⟩ := hh T hT hT1 ξ hξ hξ2
    exact ⟨u,X,hX⟩
  · have h1T : 1 ≤ T := le_of_lt (lt_of_not_ge hT1)
    apply HilbertNullExtension.exists_null (EuclideanSpace.basisFun (Fin n) ℝ)
      (EuclideanSpace.basisFun (Fin r) ℝ) hW hWm i₀ (T-1) 1 T (tsub_add_cancel_of_le h1T)
      A.toEuclideanLin.toContinuousLinearMap B.toEuclideanLin.toContinuousLinearMap
      (fun i => (C i).toEuclideanLin.toContinuousLinearMap) (fun i => (D i).toEuclideanLin.toContinuousLinearMap)
      ξ hξ hξ2
    intro η hη hη2
    obtain ⟨c₀,N,hc,hN,hh⟩ := SwitchingNullSmall.uniform_cost
      (fun i => (hW i).shift (T-1)) (fun i => CommonShiftSimple.shiftedMeas (hWm i) (T-1))
      i₀ (CommonShiftRepresentation.pair_shift hpair (T-1))
      (CommonShiftRepresentation.channels_shift hchannels (T-1)) A B C D hm hflag
    obtain ⟨u,X,hX,_⟩ := hh 1 zero_lt_one le_rfl η hη hη2
    exact ⟨u,X,hX⟩

include i₀ hpair hchannels in
theorem exactNull (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) :
    ActualControlProperties.ExactNull (𝓕:=𝓕) (EuclideanSpace.basisFun (Fin n) ℝ)
      (fun i => (hW i).toIsPreBrownianReal) hWm T
      A.toEuclideanLin.toContinuousLinearMap B.toEuclideanLin.toContinuousLinearMap
      (fun i => (C i).toEuclideanLin.toContinuousLinearMap) (fun i => (D i).toEuclideanLin.toContinuousLinearMap) := by
  intro v
  obtain ⟨u,X,hX⟩ := exists_null hW hWm i₀ hpair hchannels A B C D hm T hT hflag
    (fun _ => v) stronglyMeasurable_const (memLp_const v)
  exact ⟨u,X,SectionSolutionLinearity.SectionIntegralSolution.terminal_congr
    (EuclideanSpace.basisFun (Fin n) ℝ) (fun i => (hW i).toIsPreBrownianReal) hWm T
    (fun _ => v) 0 (0 : Lp (EuclideanSpace ℝ (Fin n)) 2 μ) _ X _ hX
    (Lp.coeFn_zero (EuclideanSpace ℝ (Fin n)) 2 μ)⟩

end LinearStochastic.SwitchingNullAll
