import LinearStochastic.SwitchingFeedbackAll
import LinearStochastic.JointUsualBrownianGlobal

/-! One deterministic locally bounded piecewise matrix gain at every positive
horizon, with actual ordinary-progressive finite-energy feedback and terminal
zero for every initial random variable known at the original time zero. -/
set_option maxHeartbeats 1500000
noncomputable section
namespace LinearStochastic.NullFeedbackTheorem
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
open CommonItoMultichannel
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

/-- A single gain schedule, independent of the initial state, realizes a
raw finite-energy null solution; the same schedule has the uniform polynomial
cost whenever the horizon is at most one. -/
def Achievement (c₀ : ℝ) (N : ℕ) (T : ℝ≥0) : Prop :=
  ∃ (a δ : ℝ≥0) (K : ℕ → Matrix (Fin r) (Fin n) ℝ), a + δ = T ∧ 0 < δ ∧
    (∀ s : ℝ≥0, s < T → ∃ M : ℝ, 0 ≤ M ∧ ∀ t, t ≤ s →
      ‖ShiftedSwitchingGain.gain a δ (fun j => (K j).toEuclideanLin.toContinuousLinearMap) t‖ ≤ M) ∧
    ∀ (ξ : Ω → EuclideanSpace ℝ (Fin n)), StronglyMeasurable[𝓕 0] ξ → MemLp ξ 2 μ →
    ∃ (u : Lp (EuclideanSpace ℝ (Fin r)) 2 (spacetimeMeasure 𝓕 μ T))
      (X : Lp (EuclideanSpace ℝ (Fin n)) 2 (spacetimeMeasure 𝓕 μ T))
      (R : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n)),
      ProgressiveControlSection.RawSolution (EuclideanSpace.basisFun (Fin n) ℝ)
        (fun i => (hW i).toIsPreBrownianReal) hWm T ξ
        A.toEuclideanLin.toContinuousLinearMap B.toEuclideanLin.toContinuousLinearMap
        (fun i => (C i).toEuclideanLin.toContinuousLinearMap) (fun i => (D i).toEuclideanLin.toContinuousLinearMap)
        (ShiftedFeedbackIdentity.feedback a δ (fun j => (K j).toEuclideanLin.toContinuousLinearMap) R)
        R u X ∧ R T =ᵐ[μ] 0 ∧
      (T ≤ 1 → (∫ s in Set.Ioc 0 (T:ℝ), ∫ ω,
        ‖ShiftedFeedbackIdentity.feedback a δ (fun j => (K j).toEuclideanLin.toContinuousLinearMap)
          R s.toNNReal ω‖^2 ∂μ) ≤ (c₀/(T:ℝ)^N)*(∫ ω, ‖ξ ω‖^2 ∂μ))

include i₀ hpair hchannels in
/-- The all-horizon gain and the small-time cost concern the same selected
schedule, with constants chosen before the horizon and every initial state. -/
theorem all_horizons (hm : 0 < m)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) :
    ∃ (c₀ : ℝ) (N : ℕ), 0 < c₀ ∧ 1 ≤ N ∧ ∀ T : ℝ≥0, 0 < T →
      Achievement (𝓕:=𝓕) hW hWm A B C D c₀ N T := by
  obtain ⟨c₀,N,hc,hN,hh⟩ := SwitchingFeedbackSmall.uniform_gain hW hWm i₀ hpair hchannels A B C D hm hflag
  refine ⟨c₀,N,hc,hN,?_⟩
  intro T hT
  by_cases hT1 : T ≤ 1
  · obtain ⟨K,_hK,hh⟩ := hh T hT hT1
    refine ⟨0,T,K,zero_add T,hT,?_,?_⟩
    · intro s hs
      exact ShiftedSwitchingGain.prefix_bound 0 T _ s (by simpa only [zero_add] using hs)
    · intro ξ hξ hξ2
      obtain ⟨u,X,R,hR,hend,he⟩ := hh ξ hξ hξ2
      have hz : ShiftedFeedbackIdentity.feedback 0 T (fun j => (K j).toEuclideanLin.toContinuousLinearMap) R =
          SwitchingFeedbackIdentity.feedback T (fun j => (K j).toEuclideanLin.toContinuousLinearMap) R := by
        funext t ω
        simp only [ShiftedFeedbackIdentity.feedback,SwitchingFeedbackIdentity.feedback,
          ShiftedSwitchingGain.gain,zero_le,if_true,tsub_zero]
      refine ⟨u,X,R,?_,hend,?_⟩
      · simpa only [hz] using hR
      · intro _
        simpa only [hz] using he
  · obtain ⟨a,δ,K,ha,hδ,_hδ1,hK,hh⟩ := SwitchingFeedbackAll.exists_gain hW hWm i₀ hpair hchannels
      A B C D hm T hT hflag
    refine ⟨a,δ,K,ha,hδ,hK,?_⟩
    intro ξ hξ hξ2
    obtain ⟨u,X,R,hR,hend⟩ := hh ξ hξ hξ2
    exact ⟨u,X,R,hR,hend,fun ht => False.elim (hT1 ht)⟩

end LinearStochastic.NullFeedbackTheorem

namespace LinearStochastic.UsualNullFeedbackTheorem
open MeasureTheory ProbabilityTheory
open scoped NNReal
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ] [μ.IsComplete] {n r m : ℕ}
  {W : Fin m → ℝ≥0 → Ω → ℝ} (hW : ∀ i, IsBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t)) (hInd : iIndepFun (fun i ω t => W i t ω) μ)

/-- The complete feedback theorem on the original usual joint Brownian
filtration. All forward and paired independence conditions are discharged. -/
theorem paper_theorem (hn : 0 < n) (hm : 0 < m)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hflag : (AdjointCoefficients.fromMatrices A B C D).flag n = ⊥) :
    letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
    ∃ (c₀ : ℝ) (N : ℕ), 0 < c₀ ∧ 1 ≤ N ∧ ∀ T : ℝ≥0, 0 < T →
      NullFeedbackTheorem.Achievement (𝓕:=JointUsualNatural.usual (μ:=μ) W hWm) hW hWm A B C D c₀ N T := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  letI : ∀ i, CommonItoIsometry.ForwardIndependent (W i) (JointUsualNatural.usual (μ:=μ) W hWm) μ :=
      JointUsualBrownianGlobal.coordinateForward hW hWm hInd
  exact NullFeedbackTheorem.all_horizons hW hWm ⟨0,hm⟩
    (JointUsualBrownianGlobal.pairForward hW hWm hInd)
    (fun i j hij => hInd.indepFun hij) A B C D hm hflag

end LinearStochastic.UsualNullFeedbackTheorem
