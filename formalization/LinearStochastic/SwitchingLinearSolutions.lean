import LinearStochastic.HilbertSwitchingUniqueness
import LinearStochastic.SectionSolutionLinearity

/-! Actual singular feedback solution classes are closed under addition and
scaling; their control is unique. These facts justify linearity of the selected
null control instead of assuming that a choice of witnesses is linear. -/
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.SwitchingLinearSolutions
open MeasureTheory ProbabilityTheory
open scoped NNReal InnerProductSpace
open CommonItoMultichannel SectionLinearDuality SectionSolutionLinearity SwitchingTimeMesh SwitchingFeedbackIdentity
variable {Ω E U κ τ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [Fintype κ] [Fintype τ] [Fintype ι]
  (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (T : ℝ≥0) (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E)
  (K : ℕ → E →L[ℝ] U)

structure Good (x : E) (u : Lp U 2 (spacetimeMeasure 𝓕 μ T))
    (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) : Prop where
  solution : SectionIntegralSolution b (fun i => (hW i).toIsPreBrownianReal) hWm T (fun _ => x)
    (A.compLp X+B.compLp u) (fun i => (C i).compLp X+(D i).compLp u) X (0 : Ω → E)
  window : ∀ j, VectorH2Extension.shift c (time T j) (duration T j) T (mesh_inside T j) u =
    (K j).compLp (VectorH2Extension.shift b (time T j) (duration T j) T (mesh_inside T j) X)

omit [CompleteSpace E] [𝓕.IsComplete μ] in
theorem add_good {x y : E} {u v : Lp U 2 (spacetimeMeasure 𝓕 μ T)}
    {X Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)}
    (q : Good b c hW hWm T A B C D K x u X) (r : Good b c hW hWm T A B C D K y v Y) :
    Good b c hW hWm T A B C D K (x+y) (u+v) (X+Y) := by
  constructor
  · have hh := SectionIntegralSolution.add b (fun i => (hW i).toIsPreBrownianReal) hWm T
      (fun _ => x) (fun _ => y) (A.compLp X+B.compLp u) (A.compLp Y+B.compLp v) X Y
      (fun i => (C i).compLp X+(D i).compLp u) (fun i => (C i).compLp Y+(D i).compLp v)
      0 0 q.solution r.solution
    have hd : A.compLp (X+Y)+B.compLp (u+v) =
        (A.compLp X+B.compLp u)+(A.compLp Y+B.compLp v) := by
      simp only [←ContinuousLinearMap.compLpₗ_apply,map_add]; abel
    have hz : (fun i => (C i).compLp (X+Y)+(D i).compLp (u+v)) =
        (fun i => (C i).compLp X+(D i).compLp u)+(fun i => (C i).compLp Y+(D i).compLp v) := by
      funext i; simp only [Pi.add_apply,←ContinuousLinearMap.compLpₗ_apply,map_add]; abel
    simpa only [←hd,←hz,zero_add,Pi.add_def] using hh
  · intro j
    simp only [map_add,q.window j,r.window j,←ContinuousLinearMap.compLpₗ_apply,map_add]

omit [𝓕.IsComplete μ] in
theorem smul_good (a : ℝ) {x : E} {u : Lp U 2 (spacetimeMeasure 𝓕 μ T)}
    {X : Lp E 2 (spacetimeMeasure 𝓕 μ T)}
    (q : Good b c hW hWm T A B C D K x u X) :
    Good b c hW hWm T A B C D K (a • x) (a • u) (a • X) := by
  constructor
  · have hh := SectionIntegralSolution.smul b (fun i => (hW i).toIsPreBrownianReal) hWm T a
      (fun _ => x) 0 (A.compLp X+B.compLp u) X
      (fun i => (C i).compLp X+(D i).compLp u) q.solution
    have hd : A.compLp (a • X)+B.compLp (a • u) = a • (A.compLp X+B.compLp u) := by
      simp only [←ContinuousLinearMap.compLpₗ_apply,map_smul,smul_add]
    have hz : (fun i => (C i).compLp (a • X)+(D i).compLp (a • u)) =
        a • (fun i => (C i).compLp X+(D i).compLp u) := by
      funext i; simp only [Pi.smul_apply,←ContinuousLinearMap.compLpₗ_apply,map_smul,smul_add]
    simpa only [←hd,←hz,smul_zero,Pi.smul_def] using hh
  · intro j
    simp only [map_smul,q.window j,←ContinuousLinearMap.compLpₗ_apply,map_smul]

include c in
theorem control_unique (i₀ : ι) (hT : 0 < T) {x : E}
    {u v : Lp U 2 (spacetimeMeasure 𝓕 μ T)} {X Y : Lp E 2 (spacetimeMeasure 𝓕 μ T)}
    (q : Good b c hW hWm T A B C D K x u X) (r : Good b c hW hWm T A B C D K x v Y) : u=v := by
  have hXY := HilbertSwitchingUniqueness.state_unique b c hW hWm i₀ T A B C D
    (fun _ => x) stronglyMeasurable_const (memLp_const x) u v X Y 0 0 q.solution r.solution K q.window r.window
  obtain ⟨R,hp,hc,h2,hr,hi,hend,he⟩ := HilbertBrownianRealization.exists_realization b c hW hWm
    i₀ T A B C D (fun _ => x) stronglyMeasurable_const (memLp_const x) u X 0 q.solution
  have hu := SwitchingFeedbackIdentity.feedback_ae b c T hT K u X R hr q.window
  have hrY : (Y : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry R := by
    rwa [←hXY]
  have hv := SwitchingFeedbackIdentity.feedback_ae b c T hT K v Y R hrY r.window
  apply Lp.ext
  exact (Lp.stronglyMeasurable u).ae_eq_trim_of_stronglyMeasurable 𝓕.predictable_le_prod
    (Lp.stronglyMeasurable v) (hu.trans hv.symm)

end LinearStochastic.SwitchingLinearSolutions
