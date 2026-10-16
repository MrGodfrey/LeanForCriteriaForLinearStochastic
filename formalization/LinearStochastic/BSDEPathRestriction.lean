import LinearStochastic.BSDEPathPaste
import LinearStochastic.CommonSolutionRestriction

/-! Exact prefixes and deterministic restarts of actual backward solutions,
with genuine endpoint random variables and H²-class reconstruction. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.BSDEPathRestriction
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard BSDEMatrixPicard BSDEPathData
open CommonHorizonRestriction CommonShiftH2 CommonShiftSimple
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ : Type*} [Fintype ι] [Fintype κ]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- The actual L² section at any time of a genuine backward solution. -/
def sectionLp (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (q : Solution (𝓕:=𝓕) hW hWm T A C η)
    (t : ℝ≥0) (ht : t ≤ T) (b : κ) : Lp ℝ 2 μ :=
  (section_memLp hW hWm T A C η q b t ht).2.toLp (q.path b t)

theorem sectionLp_ae (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (q : Solution (𝓕:=𝓕) hW hWm T A C η)
    (t : ℝ≥0) (ht : t ≤ T) (b : κ) :
    (sectionLp hW hWm T A C η q t ht b : Ω → ℝ) =ᵐ[μ] q.path b t :=
  (section_memLp hW hWm T A C η q b t ht).2.coeFn_toLp

/-- Restrict a genuine solution to its actual initial interval and endpoint. -/
def prefixSolution (i₀ : ι) (a T : ℝ≥0) (ha : a ≤ T)
    (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) (η : κ → Lp ℝ 2 μ)
    (q : Solution (𝓕:=𝓕) hW hWm T A C η) :
    Solution (𝓕:=𝓕) hW hWm a A C (sectionLp hW hWm T A C η q a ha) := by
  let X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=𝓕) (μ:=μ) a :=
    ((fun b ↦ restriction (hWm i₀) ha (q.X.1 b)),
      fun b ↦ WithLp.toLp 2 (fun i ↦ restriction (hWm i₀) ha (q.X.2 b i)))
  have hc b : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ q.path b t ω) (Iic a) :=
    (q.continuous b).mono (fun _ hω ↦ hω.mono (Iic_subset_Iic.mpr ha))
  have hd b : restriction (hWm i₀) ha (-driver T A C q.X b) = -driver a A C X b := by
    rw [map_neg]
    exact congrArg Neg.neg (BSDEPathPaste.map_driver a T
      (show H2 𝓕 μ T →L[ℝ] H2 𝓕 μ a from restriction (hWm i₀) ha) A C q.X b)
  refine ⟨X,q.path,q.progressive,hc,?_,?_,?_,?_⟩
  · intro b
    exact CommonSolutionRestriction.timeMap_S2 a T id (q.path b) (fun _ ht ↦ ht.trans ha)
      (q.progressive b) (q.continuous b) (hc b) (q.squareSup b)
  · intro b
    have hm : (timeMeasure_T a).prod μ ≤ (timeMeasure_T T).prod μ :=
      Measure.prod_mono (Measure.restrict_mono (show Ioc (0:ℝ≥0) a ⊆ Ioc 0 T from fun _ ht ↦ ⟨ht.1,ht.2.trans ha⟩) le_rfl) le_rfl
    have hh : (X.1 b : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T a).prod μ] (q.X.1 b) :=
      ae_of_ae_trim 𝓕.predictable_le_prod (restriction_ae (hWm i₀) ha (q.X.1 b))
    exact hh.trans ((q.representative b).filter_mono (ae_mono hm))
  · intro b
    exact (sectionLp_ae hW hWm T A C η q a ha b).symm
  · intro b
    have he := CommonIntegralRestriction.restrict_equation hW hWm i₀ a T ha (q.path b 0)
      (-driver T A C q.X b) (fun i ↦ q.X.2 b i) (q.path b) (q.equation b)
    rw [hd] at he
    exact he

/-- A true deterministic restart has the original terminal random variable,
actual translated state/noise classes and the full shifted filtration. -/
def shifted (a δ : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η : κ → Lp ℝ 2 μ) (q : Solution (𝓕:=𝓕) hW hWm (a+δ) A C η) :
    Solution (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
      δ A C η := by
  let X : PairH2 (κ:=κ) (ι:=ι) (𝓕:=CommonTimeShift.filtration 𝓕 a) (μ:=μ) δ :=
    ((fun b ↦ shiftCLM a δ (a+δ) le_rfl (q.X.1 b)),
      fun b ↦ WithLp.toLp 2 (fun i ↦ shiftCLM a δ (a+δ) le_rfl (q.X.2 b i)))
  let R := fun b t ↦ q.path b (a+t)
  have hp b : IsProgressive (CommonTimeShift.filtration 𝓕 a) (R b) :=
    CommonTimeShift.progressive (q.progressive b) a
  have hm : MapsTo (fun t ↦ a+t) (Iic δ) (Iic (a+δ)) := by
    intro t ht
    exact show a+t ≤ a+δ from add_le_add le_rfl ht
  have hc b : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ R b t ω) (Iic δ) :=
    (q.continuous b).mono (fun _ hω ↦ hω.comp (continuous_const.add continuous_id).continuousOn hm)
  have hd b : shiftCLM a δ (a+δ) le_rfl (-driver (a+δ) A C q.X b) = -driver δ A C X b := by
    rw [map_neg]
    exact congrArg Neg.neg (BSDEPathPaste.map_driver δ (a+δ)
      (show H2 𝓕 μ (a+δ) →L[ℝ] H2 (CommonTimeShift.filtration 𝓕 a) μ δ from
        shiftCLM a δ (a+δ) le_rfl) A C q.X b)
  refine ⟨X,R,hp,hc,?_,?_,q.terminal,?_⟩
  · intro b
    exact CommonSolutionRestriction.timeMap_S2 δ (a+δ) (fun t ↦ a+t) (q.path b) hm
      (hp b) (q.continuous b) (hc b) (q.squareSup b)
  · intro b
    exact (shift_ae a δ (a+δ) le_rfl (q.X.1 b)).trans (pull_ae a δ (a+δ) le_rfl (q.representative b))
  · intro b
    have he := CommonIntegralRestriction.shift_equation hW hWm a δ (a+δ) le_rfl
      (q.path b 0) (-driver (a+δ) A C q.X b) (fun i ↦ q.X.2 b i) (q.path b) (q.equation b)
    rw [hd] at he
    simpa only [R,add_zero] using he

/-- A terminal representative may change only by equality of its actual L² class. -/
def withTerminal (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ)
    (η ζ : κ → Lp ℝ 2 μ) (q : Solution (𝓕:=𝓕) hW hWm T A C η)
    (he : η = ζ) : Solution (𝓕:=𝓕) hW hWm T A C ζ := by
  refine ⟨q.X,q.path,q.progressive,q.continuous,q.squareSup,q.representative,?_,q.equation⟩
  intro b
  simpa only [he] using q.terminal b

omit [Fintype ι] in
/-- Prefix and translated second piece determine an actual global H² class.
This is proved by exact time-measure decomposition and inverse clock transport. -/
theorem h2_ext (i₀ : ι) (a δ : ℝ≥0) (f g : H2 𝓕 μ (a+δ))
    (hpre : restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl) f =
      restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl) g)
    (hshift : shiftCLM a δ (a+δ) le_rfl f = shiftCLM a δ (a+δ) le_rfl g) : f = g := by
  have hp : (f : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T a).prod μ] g := by
    have hf : (restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl) f : ℝ≥0 × Ω → ℝ)
        =ᵐ[(timeMeasure_T a).prod μ] f :=
      ae_of_ae_trim 𝓕.predictable_le_prod (restriction_ae (hWm i₀) (le_add_right le_rfl) f)
    have hg : (restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl) g : ℝ≥0 × Ω → ℝ)
        =ᵐ[(timeMeasure_T a).prod μ] g :=
      ae_of_ae_trim 𝓕.predictable_le_prod (restriction_ae (hWm i₀) (le_add_right le_rfl) g)
    rw [hpre] at hf
    exact hf.symm.trans hg
  have hs : (fun z : ℝ≥0 × Ω ↦ f (a+z.1,z.2)) =ᵐ[(timeMeasure_T δ).prod μ]
      (fun z ↦ g (a+z.1,z.2)) := by
    have hf := shift_ae a δ (a+δ) le_rfl f
    rw [show shift a δ (a+δ) le_rfl f = shift a δ (a+δ) le_rfl g from hshift] at hf
    exact hf.symm.trans (shift_ae a δ (a+δ) le_rfl g)
  have hb : (f : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure.restrict (Ioc a (a+δ))).prod μ] g := by
    have hh := ((CommonH2Paste.sub_interval a δ).prod (MeasurePreserving.id μ)).quasiMeasurePreserving.ae hs
    have ht : ∀ᵐ t ∂timeMeasure.restrict (Ioc a (a+δ)), a ≤ t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.1.le
    filter_upwards [hh,Measure.quasiMeasurePreserving_fst.ae ht] with z hz ht
    change f (a+(z.1-a),z.2) = g (a+(z.1-a),z.2) at hz
    rw [add_tsub_cancel_of_le ht] at hz
    exact hz
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
    𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
  rw [CommonH2Paste.time_split,Measure.add_prod]
  exact ae_add_measure_iff.mpr ⟨hp,hb⟩

end LinearStochastic.BSDEPathRestriction
