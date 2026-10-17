module

public import LinearStochastic.HilbertFullS2Bound

@[expose] public section

/-! The full-path bound in the manuscript's literal expected-energy form:
E sup_{0≤t≤T} ‖Y_t‖² ≤ C_T (E ‖ξ‖² + E ∫₀ᵀ ‖v_t‖² dt).
Both sides use the actual raw ordinary-progressive path and control. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.HilbertS2Energy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel ProgressiveControlSection

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Genuine Hilbert L² energy, with the Hilbert norm inside the integral. -/
theorem lp_energy (f : Lp E 2 μ) : ‖f‖^2=∫ ω,‖f ω‖^2 ∂μ := by
  rw [←real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- The initial class has exactly the energy of the supplied random variable. -/
theorem initial_energy (ξ : Ω → E) (hξ : MemLp ξ 2 μ) :
    ‖hξ.toLp ξ‖^2=∫ ω,‖ξ ω‖^2 ∂μ := by
  rw [lp_energy]
  exact integral_congr_ae (hξ.coeFn_toLp.fun_comp (fun x=>‖x‖^2))

/-- Predictable representative energy equals the original ordinary
progressive control energy on the real time interval. -/
theorem control_energy [IsProbabilityMeasure μ] {𝓕 : Filtration ℝ≥0 mΩ}
    (T : ℝ≥0) (v : ℝ≥0 → Ω → E) (u : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hv : MemLp (Function.uncurry v) 2 ((CommonItoCLM.timeMeasure_T T).prod μ))
    (hu : (u : ℝ≥0 × Ω → E) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry v) :
    ‖u‖^2=∫ ω,(∫ t in Ioc 0 (T:ℝ),‖v t.toNNReal ω‖^2) ∂μ := by
  calc
    ‖u‖^2=∫ z,‖u z‖^2 ∂(spacetimeMeasure 𝓕 μ T) := lp_energy (mΩ:=𝓕.predictable) u
    _=∫ z,‖u z‖^2 ∂(CommonItoCLM.timeMeasure_T T).prod μ :=
      by simpa only [Pi.pow_apply,spacetimeMeasure] using
        (integral_trim (μ:=(CommonItoCLM.timeMeasure_T T).prod μ) 𝓕.predictable_le_prod
          ((Lp.stronglyMeasurable u).norm.pow 2)).symm
    _=∫ z,‖v z.1 z.2‖^2 ∂(CommonItoCLM.timeMeasure_T T).prod μ :=
      integral_congr_ae (hu.fun_comp (fun x=>‖x‖^2))
    _=∫ ω,∫ s,‖v s ω‖^2 ∂CommonItoCLM.timeMeasure_T T ∂μ :=
      integral_prod_symm _ (hv.integrable_norm_pow (by decide))
    _=∫ ω,(∫ t in Ioc 0 (T:ℝ),‖v t.toNNReal ω‖^2) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun ω=>(RealTimeBridge.integral_real_extension T (fun s=>‖v s ω‖^2)).symm)

variable {U κ τ ι : Type*} [IsProbabilityMeasure μ]
  [CompleteSpace E] [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [Fintype κ] [Fintype τ] [Fintype ι] (b : OrthonormalBasis κ ℝ E) (c : OrthonormalBasis τ ℝ U)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

include c in
omit [CompleteSpace U] in
/-- Every actual solution obeys the uniform whole-path estimate in the
paper's exact norm and time-integral conventions. The constant is chosen
before the random initial state, control and solution. -/
theorem full_energy_bound (i₀ : ι) (T : ℝ≥0)
    (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) (D : ι → U →L[ℝ] E) :
    ∃ K : ℝ, 0<K ∧ ∀ (ξ : Ω → E) (_hξ : StronglyMeasurable[𝓕 0] ξ) (_hξ2 : MemLp ξ 2 μ)
      (v : ℝ≥0 → Ω → U) (R : ℝ≥0 → Ω → E)
      (u : Lp U 2 (spacetimeMeasure 𝓕 μ T)) (X : Lp E 2 (spacetimeMeasure 𝓕 μ T)),
      RawSolution b (fun i=>(hW i).toIsPreBrownianReal) hWm T ξ A B C D v R u X →
      (∫ ω,(⨆ t : Iic T, ‖R t.val ω‖^2) ∂μ) ≤
        K*((∫ ω,‖ξ ω‖^2 ∂μ)+(∫ ω,(∫ t in Ioc 0 (T:ℝ),‖v t.toNNReal ω‖^2) ∂μ)) := by
  obtain ⟨K,_hKdef,hK,hbound⟩ := HilbertFullS2Bound.full_bound (𝓕:=𝓕) b c hW hWm i₀ T A B C D
  refine ⟨2*K^2+1,by positivity,?_⟩
  intro ξ hξ hξ2 v R u X hR
  rw [integral_congr_ae (hR.continuous.mono (fun ω hc=>PathSupNorm.square_sup T R ω hc))]
  have hh := hbound ξ hξ hξ2 v R u X hR
  have hs := (sq_le_sq₀ (PathSupNorm.nonneg (μ:=μ) R T)
    (mul_nonneg hK (add_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr hh
  rw [PathSupNorm.sq_eq_integral T R hR.squareSup,mul_pow] at hs
  rw [←initial_energy ξ hξ2,←control_energy T v u hR.control_memLp hR.control_rep]
  have he : (‖hξ2.toLp ξ‖+‖u‖)^2 ≤ 2*(‖hξ2.toLp ξ‖^2+‖u‖^2) := by
    nlinarith [sq_nonneg (‖hξ2.toLp ξ‖-‖u‖)]
  exact hs.trans (by nlinarith [mul_le_mul_of_nonneg_left he (sq_nonneg K),sq_nonneg ‖hξ2.toLp ξ‖,sq_nonneg ‖u‖])

end LinearStochastic.HilbertS2Energy
