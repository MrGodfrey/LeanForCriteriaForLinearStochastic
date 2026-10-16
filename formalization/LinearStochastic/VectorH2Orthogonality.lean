import LinearStochastic.VectorH2Series

/-! Disjoint deterministic windows give actual orthogonality and exact energy
addition for the constructed global predictable controls. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.VectorH2Orthogonality
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal InnerProductSpace BigOperators
open CommonItoCLM CommonItoMultichannel VectorH2Extension
variable {Ω E κ : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype κ]
  (b : OrthonormalBasis κ ℝ E) {W : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent W 𝓕 μ] (hWm : ∀ t, Measurable (W t))

omit [IsProbabilityMeasure μ] in
/-- Actual Hilbert L² pairing equals the ambient spacetime pairing. -/
theorem inner_ambient (T : ℝ≥0) (f g : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    inner ℝ f g = ∫ z, inner ℝ (f z) (g z) ∂(timeMeasure_T T).prod μ := by
  rw [L2.inner_def]
  exact (integral_trim 𝓕.predictable_le_prod ((Lp.stronglyMeasurable f).inner (Lp.stronglyMeasurable g))).symm

/-- Two actually zero-extended controls on nonoverlapping windows are orthogonal. -/
theorem inner_extendShift_eq_zero (a δ c ε T : ℝ≥0) (h : a+δ ≤ T) (hc : c+ε ≤ T)
    (hd : a+δ ≤ c ∨ c+ε ≤ a)
    (f : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ))
    (g : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 c) μ ε)) :
    inner ℝ (extendShift b hWm a δ T h f) (extendShift b hWm c ε T hc g) = 0 := by
  rw [inner_ambient]
  apply integral_eq_zero_of_ae
  filter_upwards [extendShift_ae b hWm a δ T h f,extendShift_ae b hWm c ε T hc g] with z hf hg
  rw [hf,hg]
  by_cases hz : a < z.1 ∧ z.1 ≤ a+δ
  · have hn : ¬(c < z.1 ∧ z.1 ≤ c+ε) := by
      intro hw
      rcases hd with hd | hd
      · exact (not_lt_of_ge (hz.2.trans hd)) hw.1
      · exact (not_lt_of_ge (hw.2.trans hd)) hz.1
    simp only [if_pos hz,if_neg hn,inner_zero_right,Pi.zero_apply]
  · simp only [if_neg hz,inner_zero_left,Pi.zero_apply]

/-- Pulling an ambient vector equality into a true restart window preserves AE. -/
theorem pull_ae {F : Type*} (a δ T : ℝ≥0) (h : a+δ ≤ T)
    {f g : ℝ≥0 × Ω → F} (he : f =ᵐ[(timeMeasure_T T).prod μ] g) :
    (fun z : ℝ≥0 × Ω ↦ f (a+z.1,z.2)) =ᵐ[(timeMeasure_T δ).prod μ]
      fun z ↦ g (a+z.1,z.2) := by
  have hm : (CommonItoL2.timeMeasure.restrict (Ioc a (a+δ))).prod μ ≤ (timeMeasure_T T).prod μ :=
    Measure.prod_mono (CommonShiftMeasure.interval_le a δ T h) le_rfl
  exact ((CommonShiftMeasure.add_interval a δ).prod (MeasurePreserving.id μ)).quasiMeasurePreserving.ae
    (he.filter_mono (ae_mono hm))

/-- Restricting a control to a different nonoverlapping restart window gives zero. -/
theorem shift_extendShift_eq_zero (a δ c ε T : ℝ≥0) (h : a+δ ≤ T) (hc : c+ε ≤ T)
    (hd : a+δ ≤ c ∨ c+ε ≤ a)
    (g : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 c) μ ε)) :
    shift b a δ T h (extendShift b hWm c ε T hc g) = 0 := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
    (CommonTimeShift.filtration 𝓕 a).predictable_le_prod (Lp.stronglyMeasurable _)
  have ht : ∀ᵐ t ∂timeMeasure_T δ, 0 < t ∧ t ≤ δ := ae_restrict_mem measurableSet_Ioc
  filter_upwards [shift_ae b a δ T h (extendShift b hWm c ε T hc g),
    pull_ae a δ T h (extendShift_ae b hWm c ε T hc g),
    ae_of_ae_trim (CommonTimeShift.filtration 𝓕 a).predictable_le_prod
      (Lp.coeFn_zero E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ)),
    Measure.quasiMeasurePreserving_fst.ae ht] with z hs he hz ht
  rw [hs,he,hz]
  apply if_neg
  intro hw
  rcases hd with hd | hd
  · exact (not_lt_of_ge ((add_le_add_right ht.2 a).trans hd)) hw.1
  · exact (not_lt_of_ge (hw.2.trans hd)) (lt_add_of_pos_right a ht.1)

section Series
variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A summable pairwise orthogonal sequence satisfies the exact Hilbert energy
identity, derived from continuity of the real inner-product functionals. -/
theorem norm_tsum_sq (f : J → H) (hf : Summable f)
    (horth : ∀ i j, i ≠ j → inner ℝ (f i) (f j) = 0) :
    ‖∑' j, f j‖^2 = ∑' j, ‖f j‖^2 := by
  rw [←real_inner_self_eq_norm_sq]
  change (innerSL ℝ (∑' j, f j)) (∑' j, f j) = _
  rw [(innerSL ℝ (∑' j, f j)).map_tsum hf]
  apply tsum_congr
  intro i
  change inner ℝ (∑' j, f j) (f i) = _
  rw [real_inner_comm]
  change (innerSL ℝ (f i)) (∑' j, f j) = _
  rw [(innerSL ℝ (f i)).map_tsum hf,tsum_eq_single i]
  · exact real_inner_self_eq_norm_sq (f i)
  · intro j hj
    exact horth i j (Ne.symm hj)
end Series

variable [CompleteSpace E]

/-- The actual global sum of disjoint extended controls has exactly the sum
of local energies, preserving constants in quantitative control estimates. -/
theorem extensions_norm_tsum_sq (T : ℝ≥0) (a δ : ℕ → ℝ≥0) (h : ∀ j, a j+δ j ≤ T)
    (g : ∀ j, Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 (a j)) μ (δ j)))
    (hg : Summable fun j ↦ ‖g j‖)
    (hd : ∀ i j, i ≠ j → a i+δ i ≤ a j ∨ a j+δ j ≤ a i) :
    ‖∑' j, extendShift b hWm (a j) (δ j) T (h j) (g j)‖^2 = ∑' j, ‖g j‖^2 := by
  have hs := VectorH2Series.extensions_summable b hWm T a δ h g hg
  rw [norm_tsum_sq _ hs (fun i j hij ↦ inner_extendShift_eq_zero b hWm
    (a i) (δ i) (a j) (δ j) T (h i) (h j) (hd i j hij) (g i) (g j))]
  exact tsum_congr fun j ↦ congrArg (fun x : ℝ ↦ x^2) (extendShift_norm b hWm (a j) (δ j) T (h j) (g j))
/-- The global H² sum recovers exactly its local control on every window. -/
theorem shift_tsum_extensions (T : ℝ≥0) (a δ : ℕ → ℝ≥0) (h : ∀ j, a j+δ j ≤ T)
    (g : ∀ j, Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 (a j)) μ (δ j)))
    (hg : Summable fun j ↦ ‖g j‖)
    (hd : ∀ i j, i ≠ j → a i+δ i ≤ a j ∨ a j+δ j ≤ a i) (i : ℕ) :
    shift b (a i) (δ i) T (h i)
      (∑' j, extendShift b hWm (a j) (δ j) T (h j) (g j)) = g i := by
  rw [(shift b (a i) (δ i) T (h i)).map_tsum (VectorH2Series.extensions_summable b hWm T a δ h g hg),
    tsum_eq_single i]
  · exact shift_extendShift b hWm (a i) (δ i) T (h i) (g i)
  · intro j hj
    exact shift_extendShift_eq_zero b hWm (a i) (δ i) (a j) (δ j) T (h i) (h j) (hd i j (Ne.symm hj)) (g j)
end LinearStochastic.VectorH2Orthogonality
