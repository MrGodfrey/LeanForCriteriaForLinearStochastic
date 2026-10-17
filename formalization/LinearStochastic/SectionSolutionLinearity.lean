module

public import LinearStochastic.SectionSolutionNaturality

@[expose] public section

/-! Linearity of actual sectionwise stochastic integral solutions. It is
proved from Lebesgue integrability and the constructed Itô linear maps. -/
noncomputable section
namespace LinearStochastic.SectionSolutionLinearity
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel VectorItoProduct VectorItoNaturality LinearDuality SectionLinearDuality

section Drift
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {𝓕 : Filtration ℝ≥0 mΩ}

omit [CompleteSpace E] [NormedSpace ℝ E] in
theorem real_add_ae (T : ℝ≥0) (f g : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    (fun z : ℝ × Ω => (f+g) (z.1.toNNReal,z.2)) =ᵐ[
      (volume.restrict (Ioc 0 (T : ℝ))).prod μ]
      fun z => f (z.1.toNNReal,z.2) + g (z.1.toNNReal,z.2) := by
  have h := ae_eq_of_ae_eq_trim (hm := 𝓕.predictable_le_prod) (Lp.coeFn_add f g)
  exact ((RealTimeBridge.toNNReal_measurePreserving T).prod
    (MeasurePreserving.id μ)).quasiMeasurePreserving.ae_eq_comp h

omit [CompleteSpace E] in
theorem primitive_add_ae (T : ℝ≥0) (s : ℝ) (hs : s ≤ T)
    (f g : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    (fun ω => ∫ t in Ioc 0 s, (f+g) (t.toNNReal,ω)) =ᵐ[μ]
      fun ω => (∫ t in Ioc 0 s, f (t.toNNReal,ω)) + (∫ t in Ioc 0 s, g (t.toNNReal,ω)) := by
  have he := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae (real_add_ae T f g))
  have hf := ((RealTimeBridge.predictable_memLp_real_extension T μ 𝓕 f).integrable one_le_two).prod_left_ae
  have hg := ((RealTimeBridge.predictable_memLp_real_extension T μ 𝓕 g).integrable one_le_two).prod_left_ae
  filter_upwards [he,hf,hg] with ω he hf hg
  have hsub : Ioc (0 : ℝ) s ⊆ Ioc 0 (T : ℝ) := Ioc_subset_Ioc_right hs
  change (fun t => (f+g) (t.toNNReal,ω)) =ᵐ[volume.restrict (Ioc 0 (T:ℝ))]
    (fun t => f (t.toNNReal,ω) + g (t.toNNReal,ω)) at he
  rw [integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hsub he)]
  exact integral_add (IntegrableOn.mono_set hf hsub) (IntegrableOn.mono_set hg hsub)
end Drift

variable {Ω E κ ι : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [Fintype κ] [Fintype ι] (b : OrthonormalBasis κ ℝ E)
  {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

omit [CompleteSpace E] in
theorem vectorProcess_add_ae (T t : ℝ≥0)
    (φ ψ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    vectorProcess b hW hWm T (φ+ψ) t =ᵐ[μ]
      fun ω => vectorProcess b hW hWm T φ t ω + vectorProcess b hW hWm T ψ t ω := by
  have he : vectorLp b hW hWm T t (φ+ψ) = vectorLp b hW hWm T t φ + vectorLp b hW hWm T t ψ := by
    simp only [vectorLp,Pi.add_apply,map_add,Finset.sum_add_distrib]
  have ha := vectorProcess_ae_vectorLp b hW hWm T t (φ+ψ)
  rw [he] at ha
  filter_upwards [ha,Lp.coeFn_add (vectorLp b hW hWm T t φ) (vectorLp b hW hWm T t ψ),
    vectorProcess_ae_vectorLp b hW hWm T t φ,vectorProcess_ae_vectorLp b hW hWm T t ψ]
    with ω ha hab hφ hψ
  rw [ha,hab,Pi.add_apply,hφ,hψ]

omit [CompleteSpace E] in
theorem integralState_add_ae (T : ℝ≥0) (s : ℝ) (hs : s ≤ T) (ξ η : Ω → E)
    (f g : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (φ ψ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    integralState b hW hWm T (ξ+η) (f+g) (φ+ψ) s =ᵐ[μ]
      fun ω => integralState b hW hWm T ξ f φ s ω + integralState b hW hWm T η g ψ s ω := by
  filter_upwards [primitive_add_ae T s hs f g,vectorProcess_add_ae b hW hWm T s.toNNReal φ ψ]
    with ω hd hi
  simp only [integralState,hd,hi,Pi.add_apply]
  abel

omit [CompleteSpace E] in
/-- Adding actual solutions adds their initial values, drift, diffusion and
separately specified terminal values. -/
theorem SectionIntegralSolution.add (T : ℝ≥0) (ξ η : Ω → E)
    (f g X Y : Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (φ ψ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T)) (XT YT : Ω → E)
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT)
    (hY : SectionIntegralSolution b hW hWm T η g ψ Y YT) :
    SectionIntegralSolution b hW hWm T (ξ+η) (f+g) (φ+ψ) (X+Y) (XT+YT) := by
  constructor
  · filter_upwards [hX.sections,hY.sections,Measure.ae_ae_of_ae_prod (real_add_ae T X Y),
      ae_restrict_mem measurableSet_Ioc] with s hx hy ha hs
    filter_upwards [hx,hy,ha,integralState_add_ae b hW hWm T s hs.2 ξ η f g φ ψ]
      with ω hx hy ha he
    rw [ha,hx,hy,he]
  · filter_upwards [hX.terminal,hY.terminal,integralState_add_ae b hW hWm T T le_rfl ξ η f g φ ψ]
      with ω hx hy he
    simp only [Pi.add_apply]
    rw [hx,hy,he]

/-- A scalar multiple preserves the genuine integral solution, including both
endpoints. -/
theorem SectionIntegralSolution.smul (T : ℝ≥0) (a : ℝ) (ξ XT : Ω → E)
    (f X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT) :
    SectionIntegralSolution b hW hWm T (a • ξ) (a • f) (a • φ) (a • X) (a • XT) := by
  have hi (g : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
      (ContinuousLinearMap.id ℝ E).compLp g = g := by
    apply Lp.ext
    exact (ContinuousLinearMap.id ℝ E).coeFn_compLp g
  have h := SectionSolutionNaturality.SectionIntegralSolution.map b hW hWm T
    (a • ContinuousLinearMap.id ℝ E) ξ f φ X XT hX
  simpa only [ContinuousLinearMap.smul_compLp,hi,smul_apply,
    ContinuousLinearMap.id_apply,Pi.smul_def] using h

omit [CompleteSpace E] in
/-- The zero state, initial value, drift, diffusion and terminal value really
satisfy the integral equation at every horizon. -/
theorem zero_solution (T : ℝ≥0) :
    SectionIntegralSolution (𝓕:=𝓕) b hW hWm T (0 : Ω → E) 0 (fun _ => 0) 0 0 := by
  have hstate (s : ℝ) (hs : s ≤ T) :
      integralState (𝓕:=𝓕) b hW hWm T (0 : Ω → E) 0 (fun _ => 0) s =ᵐ[μ] 0 := by
    have hd := primitive_add_ae (𝓕:=𝓕) (μ:=μ) (E:=E) T s hs 0 0
    simp only [add_zero] at hd
    have hi := vectorProcess_ae_vectorLp (𝓕:=𝓕) b hW hWm T s.toNNReal (fun _ => 0)
    simp only [vectorLp,map_zero,Finset.sum_const_zero] at hi
    have hz := hi.trans (Lp.coeFn_zero E 2 μ)
    filter_upwards [hd,hz] with ω hd hz
    have hdz : (∫ t in Ioc 0 s, (0 : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (t.toNNReal,ω)) = 0 := by
      simpa only [add_eq_left] using hd.symm
    simp only [integralState,hdz,hz,Pi.zero_apply,zero_add]
  constructor
  · have hz := ae_eq_of_ae_eq_trim (hm:=𝓕.predictable_le_prod)
      (Lp.coeFn_zero E 2 (spacetimeMeasure 𝓕 μ T))
    have hr := ((RealTimeBridge.toNNReal_measurePreserving T).prod
      (MeasurePreserving.id μ)).quasiMeasurePreserving.ae_eq_comp hz
    filter_upwards [Measure.ae_ae_of_ae_prod hr,ae_restrict_mem measurableSet_Ioc] with s hs hsm
    exact Filter.EventuallyEq.trans hs (hstate s hsm.2).symm
  · exact (hstate T le_rfl).symm

omit [CompleteSpace E] in
/-- Replacing only the separately specified endpoint by an almost-everywhere
identical random variable preserves the actual solution. -/
theorem SectionIntegralSolution.terminal_congr (T : ℝ≥0) (ξ XT YT : Ω → E)
    (f X : Lp E 2 (spacetimeMeasure 𝓕 μ T)) (φ : ι → Lp E 2 (spacetimeMeasure 𝓕 μ T))
    (hX : SectionIntegralSolution b hW hWm T ξ f φ X XT) (hT : YT =ᵐ[μ] XT) :
    SectionIntegralSolution b hW hWm T ξ f φ X YT :=
  ⟨hX.sections,hT.trans hX.terminal⟩

end LinearStochastic.SectionSolutionLinearity
