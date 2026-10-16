import LinearStochastic.CommonItoS2
import BrownianMotion.StochasticIntegral.Predictable

noncomputable section
namespace LinearStochastic.CommonFiltrationCompletion
open MeasureTheory ProbabilityTheory Set
open CommonNullAugmentation CommonItoIsometry
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Adding ambient-measurable null events preserves genuine independence. -/
theorem indep_sup_nulls {m₁ m₂ : MeasurableSpace Ω} (h : Indep m₁ m₂ μ) :
    Indep (m₁ ⊔ nullsAlg mΩ μ) m₂ μ := by
  rw [Indep_iff] at h ⊢
  intro s t hs ht
  obtain ⟨s',hs',he⟩ := exists_ae_eq_of_sup_nulls hs
  rw [measure_congr (ae_eq_set_inter he (ae_eq_refl t)), measure_congr he]
  exact h s' t hs' ht

/-- Independence depends only on the actual random variable up to a.e. equality. -/
theorem indep_comap_congr {E : Type*} [MeasurableSpace E] {m : MeasurableSpace Ω}
    {f g : Ω → E} (he : f =ᵐ[μ] g)
    (h : Indep m (MeasurableSpace.comap f inferInstance) μ) :
    Indep m (MeasurableSpace.comap g inferInstance) μ := by
  rw [Indep_iff] at h ⊢
  intro s t hs ht
  obtain ⟨u,hu,rfl⟩ := ht
  have hpre : f ⁻¹' u =ᵐ[μ] g ⁻¹' u := he.preimage _
  rw [← measure_congr (ae_eq_set_inter (ae_eq_refl s) hpre), ← measure_congr hpre]
  exact h s (f ⁻¹' u) hs ⟨u,hu,rfl⟩

/-- The explicit common-filtration independence assumptions remain true after
adjoining ambient null events. No Brownian law or integral conclusion is used. -/
theorem forwardIndependent_sup_nulls {B : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    [hF : ForwardIndependent B 𝓕 μ] :
    ForwardIndependent B (𝓕 ⊔ Filtration.const ℝ≥0 (nullsAlg mΩ μ) nullsAlg_le) μ where
  adapted t := (hF.adapted t).mono le_sup_left
  indep s := indep_sup_nulls (hF.indep s)

/-- A genuinely complete filtration already contains the measurable null hull. -/
theorem nullsAlg_le_complete (𝓕 : Filtration ℝ≥0 mΩ) [𝓕.IsComplete μ] (t : ℝ≥0) :
    nullsAlg mΩ μ ≤ 𝓕 t :=
  MeasurableSpace.generateFrom_le fun _ hs ↦ Filtration.IsComplete.measurableSet_of_null hs.2 t

/-- For a complete input filtration, the constructed null augmentation changes
nothing. This is a theorem about the supplied filtration, not a canonical-space substitution. -/
theorem sup_nulls_eq (𝓕 : Filtration ℝ≥0 mΩ) [𝓕.IsComplete μ] :
    𝓕 ⊔ Filtration.const ℝ≥0 (nullsAlg mΩ μ) nullsAlg_le = 𝓕 := by
  apply sup_eq_left.mpr
  intro t
  exact nullsAlg_le_complete 𝓕 t

/-- Actual a.e. modification of a measurable set is measurable in a complete
filtration, including subsets of null sets in the ambient space. -/
theorem measurableSet_of_ae_eq (𝓕 : Filtration ℝ≥0 mΩ) [𝓕.IsComplete μ]
    (t : ℝ≥0) {s u : Set Ω} (hu : MeasurableSet[𝓕 t] u) (he : s =ᵐ[μ] u) :
    MeasurableSet[𝓕 t] s := by
  have hsu : μ (s \ u) = 0 := by
    apply measure_mono_null (show s \ u ⊆ {ω | ¬ (ω ∈ s ↔ ω ∈ u)} by
      intro ω hω; exact fun h ↦ hω.2 (h.mp hω.1))
    exact ae_iff.mp he.mem_iff
  have hus : μ (u \ s) = 0 := by
    apply measure_mono_null (show u \ s ⊆ {ω | ¬ (ω ∈ s ↔ ω ∈ u)} by
      intro ω hω; exact fun h ↦ hω.2 (h.mpr hω.1))
    exact ae_iff.mp he.mem_iff
  have h1 := Filtration.IsComplete.measurableSet_of_null (𝓕:=𝓕) hsu t
  have h2 := Filtration.IsComplete.measurableSet_of_null (𝓕:=𝓕) hus t
  have hs : s = (u \ (u \ s)) ∪ (s \ u) := by ext ω; simp only [mem_union,mem_sdiff]; tauto
  rw [hs]
  exact (hu.diff h2).union h1

/-- On a genuinely complete filtration, all pointwise measurable modifications
retain adaptation. The conclusion concerns the supplied representatives. -/
theorem measurable_of_ae_eq (𝓕 : Filtration ℝ≥0 mΩ) [𝓕.IsComplete μ]
    (t : ℝ≥0) {E : Type*} [MeasurableSpace E] {f g : Ω → E}
    (hg : Measurable[𝓕 t] g) (he : f =ᵐ[μ] g) : Measurable[𝓕 t] f := by
  intro s hs
  exact measurableSet_of_ae_eq 𝓕 t (hg hs) (he.preimage _)

/-- Brownian path repair is valid on every complete common filtration: the
actual continuous modification remains adapted and has independent whole future. -/
theorem forwardIndependent_continuous_mk {B : ℝ≥0 → Ω → ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ] [hF : ForwardIndependent B 𝓕 μ]
    (hB : IsBrownianReal B μ) :
    ForwardIndependent (hB.toIsPreBrownianReal.mk B) 𝓕 μ where
  adapted t := (measurable_of_ae_eq 𝓕 t (hF.adapted t).measurable
    (hB.toIsPreBrownianReal.mk_ae_eq t)).stronglyMeasurable
  indep s := by
    apply indep_comap_congr _ (hF.indep s)
    filter_upwards [hB.mk_ae_forall_eq] with ω hω
    funext u
    rw [hω (s+u), hω s]

/-- Every Brownian motion on a complete common filtration has an everywhere
continuous indistinguishable Brownian version satisfying the same genuine
whole-forward independence assumptions on that very probability space. -/
theorem exists_continuous_brownian_version {B : ℝ≥0 → Ω → ℝ}
    {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ] [ForwardIndependent B 𝓕 μ]
    (hB : IsBrownianReal B μ) :
    ∃ W : ℝ≥0 → Ω → ℝ, IsBrownianReal W μ ∧ ForwardIndependent W 𝓕 μ ∧
      (∀ ω, Continuous fun t ↦ W t ω) ∧ (∀ᵐ ω ∂μ, ∀ t, W t ω = B t ω) :=
  ⟨hB.toIsPreBrownianReal.mk B, hB.toIsPreBrownianReal.isBrownianReal_mk,
    forwardIndependent_continuous_mk hB, hB.toIsPreBrownianReal.continuous_mk,
    hB.mk_ae_forall_eq⟩


/-- The S² construction uses the original filtration whenever it satisfies
actual completeness; no replacement probability space or extra filtration is introduced. -/
theorem exists_s2_on_complete_filtration [IsProbabilityMeasure μ]
    {B : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    [𝓕.IsComplete μ] [ForwardIndependent B 𝓕 μ]
    (hB : IsPreBrownianReal B μ) (T : ℝ≥0)
    (hBmeas : ∀ t, Measurable (B t)) (hBcont : ∀ ω, Continuous fun t : ℝ≥0 ↦ B t ω)
    (φ : Lp ℝ 2 (CommonItoCLM.trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    ∃ X : ℝ≥0 → Ω → ℝ,
      (∀ t, t ≤ T → X t =ᵐ[μ] CommonItoProcessGeneral.itoProcessCLM hB T t hBmeas φ) ∧
      (∀ ω, Continuous fun t ↦ X t ω) ∧ Martingale X 𝓕 μ ∧
      MemLp (ContinuousDoobL2.pathSup X T) 2 μ ∧
      eLpNorm (ContinuousDoobL2.pathSup X T) 2 μ ≤ 2 * ‖φ‖ₑ ∧
      Integrable (fun ω ↦ ContinuousDoobL2.pathSup X T ω ^ 2) μ := by
  have h := CommonItoS2.exists_continuous_s2_modification hB T hBmeas hBcont φ
  have he : CommonItoContinuousVersion.augFiltration (𝓕:=𝓕) (μ:=μ) hBmeas = 𝓕 :=
    sup_nulls_eq 𝓕
  rwa [he] at h

end LinearStochastic.CommonFiltrationCompletion

