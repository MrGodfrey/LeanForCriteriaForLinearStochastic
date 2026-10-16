import LinearStochastic.CommonGlobalS2Bound
import LinearStochastic.HilbertPathSupBound
import LinearStochastic.HilbertBrownianRealization
import LinearStochastic.ProgressiveControlSection

/-! Uniform full S² estimates in the original Hilbert norm for the actual
ordinary-progressive controlled paths and original Brownian drivers. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.HilbertFullS2Bound
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct LinearDuality SectionLinearDuality
open HilbertLocalSolution HilbertSectionCoordinates HilbertBrownianRealization
open ProgressiveControlSection CoordinatePathSolution
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

omit [CompleteSpace U] in
/-- The actual raw path is indistinguishable, on the whole closed horizon,
from the coordinate solution used for the quantitative Picard estimate. -/
theorem path_coordinates (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
    (ξ : Ω → E) (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
    (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hR : RawSolution b (fun i=>(hW i).toIsPreBrownianReal) hWm T ξ A B C D v R u X) (j : κ) :
    ∀ᵐ ω ∂μ, ∀ t, t≤T → inner ℝ (b j) (R t ω)=
      (coordinateSolution b c hW hWm i₀ T A B C D ξ hξ hξ2 u X (R T)
        (hR.to_section b (fun i=>(hW i).toIsPreBrownianReal) hWm T ξ A B C D v R u X)).path j t ω := by
  let q := coordinateSolution b c hW hWm i₀ T A B C D ξ hξ hξ2 u X (R T)
    (hR.to_section b (fun i=>(hW i).toIsPreBrownianReal) hWm T ξ A B C D v R u X)
  apply CommonDriftS2.indistinguishable_on_Iic T (fun t ω=>inner ℝ (b j) (R t ω)) (q.path j)
    (hR.continuous.mono (fun _ hc=>(innerSL ℝ (b j)).continuous.comp_continuousOn hc)) (q.continuous j)
  intro t ht
  have hclass : R t =ᵐ[μ] integralState b (fun i=>(hW i).toIsPreBrownianReal) hWm T ξ
      (A.compLp X+B.compLp u) (fun i=>(C i).compLp X+(D i).compLp u) (t:ℝ) := by
    filter_upwards [hR.equation t ht,primitive_ae T t (by exact_mod_cast ht) A B v R u X hR.control_rep hR.state_rep]
      with ω he hd
    simpa only [integralState,Real.toNNReal_coe,hd] using he
  have hi := (hclass.fun_comp (innerSL ℝ (b j))).trans
    (integral_coordinate_ae b (fun i=>(hW i).toIsPreBrownianReal) hWm T t (by exact_mod_cast ht)
      ξ (A.compLp X+B.compLp u) (fun i=>(C i).compLp X+(D i).compLp u) j)
  simp only [Real.toNNReal_coe,drift_coordinates b c T A B,noise_coordinates b c T C D] at hi
  filter_upwards [hi,q.equation j t ht] with ω hi hq
  rw [RealTimeBridge.integral_real_extension t (fun s=>CommonLocalSolution.driftInput T
    (coefficientMatrix b b A) (coefficientMatrix b c B) (fun j=>coordinate c j u)
    (fun j=>coordinate b j X) j (s,ω))] at hi
  exact hi.trans hq.symm

include c in
omit [CompleteSpace U] in
/-- A finite coefficient-dependent constant bounds the actual full Hilbert
S² norm on each horizon, uniformly over every F₀ L² initial state, admissible
ordinary progressive control, and actual continuous S² solution. -/
theorem full_bound (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E) :
    ∃ K : ℝ, K=(Fintype.card κ:ℝ)*CommonGlobalS2Bound.boundConstant T
      (coefficientMatrix b b A) (coefficientMatrix b c B)
      (fun i=>coefficientMatrix b b (C i)) (fun i=>coefficientMatrix b c (D i)) ∧
      0≤K ∧ ∀ (ξ : Ω → E) (_hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
      (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
      (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)),
      RawSolution b (fun i=>(hW i).toIsPreBrownianReal) hWm T ξ A B C D v R u X →
      PathSupNorm.norm (μ:=μ) R T ≤ K*(‖hξ2.toLp ξ‖+‖u‖) := by
  let K := CommonGlobalS2Bound.boundConstant T (coefficientMatrix b b A) (coefficientMatrix b c B)
    (fun i=>coefficientMatrix b b (C i)) (fun i=>coefficientMatrix b c (D i))
  have hK : 0≤K := CommonGlobalS2Bound.boundConstant_nonneg T _ _ _ _
  have hbound := CommonGlobalS2Bound.brownian_explicit_bound (𝓕:=𝓕) hWm hW i₀ T
    (coefficientMatrix b b A) (coefficientMatrix b c B)
    (fun i=>coefficientMatrix b b (C i)) (fun i=>coefficientMatrix b c (D i))
  refine ⟨(Fintype.card κ:ℝ)*K,rfl,mul_nonneg (Nat.cast_nonneg _) hK,?_⟩
  intro ξ hξ hξ2 v R u X hR
  let q := coordinateSolution b c hW hWm i₀ T A B C D ξ hξ hξ2 u X (R T)
    (hR.to_section b (fun i=>(hW i).toIsPreBrownianReal) hWm T ξ A B C D v R u X)
  have hpath : ∀ᵐ ω ∂μ, ∀ t, t≤T → R t ω=reconstruct b q.path t ω := by
    have hall : ∀ᵐ ω ∂μ, ∀ j, ∀ t, t≤T → inner ℝ (b j) (R t ω)=q.path j t ω := by
      rw [ae_all_iff]
      exact path_coordinates b c hW hWm i₀ T A B C D ξ hξ hξ2 v R u X hR
    filter_upwards [hall] with ω hω
    intro t ht
    calc
      R t ω=∑ j,inner ℝ (b j) (R t ω) • b j := (b.sum_repr' _).symm
      _=reconstruct b q.path t ω := Finset.sum_congr rfl (fun j _=>by rw [hω j t ht])
  rw [PathSupNorm.congr T hpath]
  have hr := HilbertPathSupBound.reconstruction b T q.path
    (fun j=>(q.progressive j).isStronglyProgressive.stronglyAdapted) q.continuous q.squareSup
  apply hr.trans
  have hinit : ‖fun j=>((innerSL ℝ (b j)).comp_memLp' hξ2).toLp (fun ω=>inner ℝ (b j) (ξ ω))‖≤‖hξ2.toLp ξ‖ := by
    simp_rw [HilbertPathSupBound.initial_coordinate b ξ hξ2]
    exact HilbertPathSupBound.coordinates_norm b _
  have hu := HilbertPathSupBound.coordinates_norm (mΩ:=𝓕.predictable) c u
  have hcoord (j : κ) : PathSupNorm.norm (μ:=μ) (q.path j) T ≤ K*(‖hξ2.toLp ξ‖+‖u‖) :=
    (hbound _ (fun j=>(innerSL ℝ (b j)).continuous.comp_stronglyMeasurable hξ)
      (fun j=>(innerSL ℝ (b j)).comp_memLp' hξ2) _ q j).trans
      (mul_le_mul_of_nonneg_left (add_le_add hinit hu) hK)
  calc
    ∑ j,PathSupNorm.norm (μ:=μ) (q.path j) T ≤ ∑ _j:κ,K*(‖hξ2.toLp ξ‖+‖u‖) :=
      Finset.sum_le_sum (fun j _=>hcoord j)
    _=((Fintype.card κ:ℝ)*K)*(‖hξ2.toLp ξ‖+‖u‖) := by simp; ring

end LinearStochastic.HilbertFullS2Bound
