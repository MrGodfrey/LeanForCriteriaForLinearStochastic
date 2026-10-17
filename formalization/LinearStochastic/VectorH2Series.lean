module

public import LinearStochastic.VectorH2Extension

@[expose] public section

/-! Actual continuous horizon restriction and summation of isometrically
zero-extended controls. Prefix recovery is an equality of genuine L² classes. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.VectorH2Series
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonItoCLM CommonItoMultichannel VectorHorizonRestriction
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
theorem restrict_norm {t T : ℝ≥0} (h : t ≤ T) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    ‖restrict h f‖ ≤ ‖f‖ := by
  simp only [Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.memLp f).eLpNorm_lt_top.ne
  rw [eLpNorm_congr_ae (restrict_ae h f)]
  exact eLpNorm_mono_measure _ (measure_le h)

/-- The existing genuine vector restriction is a continuous linear contraction. -/
def restrictCLM {t T : ℝ≥0} (h : t ≤ T) :
    Lp E 2 (spacetimeMeasure 𝓕 μ T) →L[ℝ] Lp E 2 (spacetimeMeasure 𝓕 μ t) :=
  LinearMap.mkContinuous
    { toFun := restrict h
      map_add' := fun f g ↦ by
        apply Lp.ext
        filter_upwards [restrict_ae h (f+g),restrict_ae h f,restrict_ae h g,
          Lp.coeFn_add (restrict h f) (restrict h g),
          (Lp.coeFn_add f g).filter_mono (ae_mono (measure_le h))] with z hs hf hg ha hb
        rw [hs,ha,hb]
        simp only [Pi.add_apply,hf,hg]
      map_smul' := fun c f ↦ by
        simp only [RingHom.id_apply]
        apply Lp.ext
        filter_upwards [restrict_ae h (c • f),restrict_ae h f,Lp.coeFn_smul c (restrict h f),
          (Lp.coeFn_smul c f).filter_mono (ae_mono (measure_le h))] with z hs hf ha hb
        rw [hs,ha,hb]
        simp only [Pi.smul_apply,hf] }
    1 (fun f ↦ by
      change ‖restrict h f‖ ≤ 1*‖f‖
      simpa only [one_mul] using restrict_norm h f)

theorem restrictCLM_apply {t T : ℝ≥0} (h : t ≤ T) (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    restrictCLM h f = restrict h f := rfl

variable [CompleteSpace E] {κ : Type*} [Fintype κ]
  (b : OrthonormalBasis κ ℝ E) {W : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent W 𝓕 μ] (hWm : ∀ t, Measurable (W t))

omit [CompleteSpace E] in
/-- Exact compatibility with every containing prefix. -/
theorem restriction_extendShift (a δ s T : ℝ≥0) (hs : a+δ ≤ s) (hT : s ≤ T)
    (g : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ)) :
    restrictCLM hT (VectorH2Extension.extendShift b hWm a δ T (hs.trans hT) g) =
      VectorH2Extension.extendShift b hWm a δ s hs g := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable 𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
  have hm : (timeMeasure_T s).prod μ ≤ (timeMeasure_T T).prod μ :=
    Measure.prod_mono (Measure.restrict_mono (Ioc_subset_Ioc_right hT) le_rfl) le_rfl
  have hr : (restrictCLM hT (VectorH2Extension.extendShift b hWm a δ T (hs.trans hT) g) : ℝ≥0 × Ω → E)
      =ᵐ[(timeMeasure_T s).prod μ] (VectorH2Extension.extendShift b hWm a δ T (hs.trans hT) g) :=
    ae_of_ae_trim 𝓕.predictable_le_prod (restrict_ae hT _)
  exact hr.trans (((VectorH2Extension.extendShift_ae b hWm a δ T (hs.trans hT) g).filter_mono (ae_mono hm)).trans
    (VectorH2Extension.extendShift_ae b hWm a δ s hs g).symm)

/-- Absolutely summable actual local controls give a genuine global H² control. -/
theorem extensions_summable (T : ℝ≥0) (a δ : ℕ → ℝ≥0) (h : ∀ j, a j+δ j ≤ T)
    (g : ∀ j, Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 (a j)) μ (δ j)))
    (hg : Summable fun j ↦ ‖g j‖) :
    Summable fun j ↦ VectorH2Extension.extendShift b hWm (a j) (δ j) T (h j) (g j) := by
  apply Summable.of_norm
  simpa only [VectorH2Extension.extendShift_norm] using hg

/-- Before all later windows, the global control sum has exactly the finite
prefix of actual extended controls. This uses real continuous restriction. -/
theorem restrict_tsum_prefix (T t : ℝ≥0) (ht : t ≤ T)
    (a δ : ℕ → ℝ≥0) (h : ∀ j, a j+δ j ≤ T)
    (g : ∀ j, Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 (a j)) μ (δ j)))
    (hg : Summable fun j ↦ ‖g j‖) (N : ℕ) (hfuture : ∀ j, N ≤ j → t ≤ a j) :
    restrictCLM ht (∑' j, VectorH2Extension.extendShift b hWm (a j) (δ j) T (h j) (g j)) =
      ∑ j ∈ Finset.range N, restrictCLM ht (VectorH2Extension.extendShift b hWm (a j) (δ j) T (h j) (g j)) := by
  rw [(restrictCLM (E:=E) (𝓕:=𝓕) (μ:=μ) ht).map_tsum (extensions_summable b hWm T a δ h g hg)]
  apply tsum_eq_sum
  intro j hj
  have hjN : N ≤ j := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hj)
  exact VectorH2Extension.restriction_extendShift_zero b hWm (a j) (δ j) T t (h j) (hfuture j hjN) (g j)
end LinearStochastic.VectorH2Series
