import LinearStochastic.KnownTargetState
import LinearStochastic.KnownTargetGramian
import LinearStochastic.ProgressiveControlSection
import LinearStochastic.ZeroIntegralDrift

/-! The Gramian last-interval construction is a genuine raw controlled
solution, with ordinary progressive control and actual finite S² state. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.KnownTargetSolution
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
open DeterministicGramianControl DelayedDeterministicState KnownTargetState
open CommonItoMultichannel VectorItoProduct ProgressiveControlSection
variable {Ω E U κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (A : E →L[ℝ] E) (B : U →L[ℝ] E) (a T : ℝ≥0) (ha : a<T)
  (hK : ∀ v : E, (∀ k : ℕ, B.adjoint ((A.adjoint^k) v)=0) → v=0)

omit b hW hWm [Fintype κ] [Fintype ι] [IsProbabilityMeasure μ] mΩ in
/-- The actual exponential state reaches the given displacement exactly. -/
theorem terminal (x v : E) :
    KnownTargetState.path A B
      (kernel A B ((T:ℝ)-a) (sub_pos.mpr (NNReal.coe_lt_coe.mpr ha)) hK)
      a x (fun _ : Unit => v) T () = (NormedSpace.exp ((T:ℝ) • A)) x+v := by
  let h : ℝ := (T:ℝ)-a
  have hh : 0<h := sub_pos.mpr (NNReal.coe_lt_coe.mpr ha)
  let K := kernel A B h hh hK
  change (NormedSpace.exp ((T:ℝ) • A)) x+response A B K a T v = _
  congr 1
  rw [response,max_eq_left hh.le,responseOperator_apply A B K (kernel_continuous A B h hh hK),
    DeterministicVariation.convolution A 0 (fun s => B (K s v))
      (B.continuous.comp ((kernel_continuous A B h hh hK).clm_apply continuous_const))]
  rw [map_zero,zero_add,intervalIntegral.integral_of_le hh.le,←integral_Icc_eq_integral_Ioc]
  exact DeterministicGramianControl.terminal_integral A B h hh hK v

/-- Concrete controls and paths: the target is known at a, the control is zero
on [0,a], and the stated actual raw SDE attains it at T. -/
theorem exists_solution (x : E) (η : Ω → E)
    (hη : StronglyMeasurable[𝓕 a] η) (hη2 : MemLp η 2 μ) :
    let K := kernel A B ((T:ℝ)-a) (sub_pos.mpr (NNReal.coe_lt_coe.mpr ha)) hK
    let ξ := fun ω => η ω-(NormedSpace.exp ((T:ℝ) • A)) x
    let v := KnownTargetControl.control a T K ξ
    let R := KnownTargetState.path A B K a x ξ
    ∃ (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)),
      RawSolution b hW hWm T (fun _ => x) A B (fun _=>0) (fun _=>0) v R u X ∧
      (∀ ω, R T ω=η ω) ∧ (∀ t, t≤a → ∀ ω, v t ω=0) := by
  dsimp only
  let K := kernel A B ((T:ℝ)-a) (sub_pos.mpr (NNReal.coe_lt_coe.mpr ha)) hK
  let ξ : Ω → E := fun ω => η ω-(NormedSpace.exp ((T:ℝ) • A)) x
  let v := KnownTargetControl.control a T K ξ
  let R := KnownTargetState.path A B K a x ξ
  have hcK : Continuous K := kernel_continuous A B _ _ hK
  have hξ : StronglyMeasurable[𝓕 a] ξ := hη.sub stronglyMeasurable_const
  have hξ2 : MemLp ξ 2 μ := hη2.sub (memLp_const _)
  have hv := KnownTargetControl.progressive a T K ξ hcK hξ
  have hv2 := KnownTargetControl.memLp a T K ξ hcK hξ hξ2
  have hR := KnownTargetState.progressive A B K a x ξ hcK hξ
  have hRc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => R t ω) (Iic T) :=
    Filter.Eventually.of_forall (fun ω => (KnownTargetState.continuous A B K a x ξ hcK ω).continuousOn)
  have hR2 := KnownTargetState.squareSup A B K a T x ξ hcK hξ hξ2
  obtain ⟨u,X,hu,hX⟩ := representatives T v R hv hv2 hR hRc hR2
  have hzeroX : (0 : E →L[ℝ] E).compLp X=0 := by
    apply Lp.ext
    filter_upwards [(0 : E →L[ℝ] E).coeFn_compLp X,Lp.coeFn_zero E 2 (spacetimeMeasure 𝓕 μ T)] with z hf hz
    simp only [hf,hz,zero_apply,Pi.zero_apply]
  have hzerou : (0 : U →L[ℝ] E).compLp u=0 := by
    apply Lp.ext
    filter_upwards [(0 : U →L[ℝ] E).coeFn_compLp u,Lp.coeFn_zero E 2 (spacetimeMeasure 𝓕 μ T)] with z hf hz
    simp only [hf,hz,zero_apply,Pi.zero_apply]
  have hn : (fun _ : ι => (0:E →L[ℝ] E).compLp X+(0:U →L[ℝ] E).compLp u)=fun _=>0 := by
    rw [hzeroX,hzerou,add_zero]
  refine ⟨u,X,⟨hv,hv2,hR,hRc,hR2,hu,hX,?_⟩,?_,?_⟩
  · intro t ht
    rw [hn]
    filter_upwards [ZeroIntegralDrift.vectorProcess_zero_ae (𝓕:=𝓕) b hW hWm T t] with ω hω
    rw [hω]
    simpa only [Pi.zero_apply,add_zero,add_comm] using KnownTargetState.equation A B K a T x ξ hcK t ht ω
  · intro ω
    have he := terminal A B a T ha hK x (ξ ω)
    change R T ω=(NormedSpace.exp ((T:ℝ) • A)) x+ξ ω at he
    change R T ω=η ω
    rw [he]
    dsimp [ξ]
    abel
  · exact KnownTargetControl.zero_prefix a T K ξ

end LinearStochastic.KnownTargetSolution
