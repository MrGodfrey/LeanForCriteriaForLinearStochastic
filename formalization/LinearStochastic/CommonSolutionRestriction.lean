module

public import LinearStochastic.CommonIntegralRestriction
public import LinearStochastic.CommonSolutionFixedPoint

@[expose] public section

/-! Actual restriction and restart of continuous S² solution data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonSolutionRestriction
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonLocalSolution
open CommonSolutionData CommonHorizonRestriction CommonShiftH2 CommonShiftSimple
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

omit [IsProbabilityMeasure μ] in
/-- A deterministic clock map into a bounded horizon preserves the true path
supremum L² estimate whenever the composed process is genuinely progressive. -/
theorem timeMap_S2 {𝓖 : Filtration ℝ≥0 mΩ} (s T : ℝ≥0) (φ : ℝ≥0 → ℝ≥0)
    (R : ℝ≥0 → Ω → ℝ) (hm : MapsTo φ (Iic s) (Iic T))
    (hp : IsProgressive 𝓖 (fun t ↦ R (φ t)))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ R t ω) (Iic T))
    (hcφ : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ R (φ t) ω) (Iic s))
    (h2 : MemLp (ContinuousDoobL2.pathSup R T) 2 μ) :
    MemLp (ContinuousDoobL2.pathSup (fun t ↦ R (φ t)) s) 2 μ := by
  letI : Nonempty (Iic s) := ⟨⟨s,show s ≤ s from le_rfl⟩⟩
  apply h2.mono' (CommonStateS2.pathSup_measurableOn s hp.isStronglyProgressive.stronglyAdapted hcφ)
  filter_upwards [hc] with ω hω
  change |ContinuousDoobL2.pathSup (fun t ↦ R (φ t)) s ω| ≤ _
  have hn : 0 ≤ ContinuousDoobL2.pathSup (fun t ↦ R (φ t)) s ω := Real.iSup_nonneg fun _ ↦ norm_nonneg _
  rw [abs_of_nonneg hn]
  have hcomp : IsCompact (Iic T) := by rw [←Icc_bot]; exact isCompact_Icc
  have hb : BddAbove (range (fun t : Iic T ↦ ‖R t.val ω‖)) := by
    simpa only [image_eq_range] using hcomp.bddAbove_image hω.norm
  apply ciSup_le
  intro t
  exact le_ciSup hb ⟨φ t.val,hm t.property⟩

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- The actual prefix of any genuine solution is again a genuine solution,
with unchanged raw paths and truly restricted predictable coefficients. -/
def prefixSolution (i₀ : ι) (a T : ℝ≥0) (ha : a ≤ T)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (u : ν → H2 𝓕 μ T) (q : Solution hW hWm T A B C D ξ u) :
    Solution hW hWm a A B C D ξ (fun b ↦ restriction (hWm i₀) ha (u b)) := by
  let X := fun b ↦ restriction (hWm i₀) ha (q.X b)
  have hc b : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ q.path b t ω) (Iic a) :=
    (q.continuous b).mono (fun _ hω ↦ hω.mono (Iic_subset_Iic.mpr ha))
  have hec (M : Matrix κ κ ℝ) (N : Matrix κ ν ℝ) (b : κ) :
      restriction (hWm i₀) ha (driftInput T M N u q.X b) =
      driftInput a M N (fun c ↦ restriction (hWm i₀) ha (u c)) X b :=
    CommonPastedClasses.map_linearInput a T
      (show H2 𝓕 μ T →L[ℝ] H2 𝓕 μ a from restriction (hWm i₀) ha) M N q.X u b
  refine ⟨X,q.path,q.progressive,hc,?_,?_,q.initial,?_⟩
  · intro b
    exact timeMap_S2 a T id (q.path b) (fun _ ht ↦ ht.trans ha) (q.progressive b) (q.continuous b) (hc b) (q.squareSup b)
  · intro b
    have hm : (timeMeasure_T a).prod μ ≤ (timeMeasure_T T).prod μ :=
      Measure.prod_mono (Measure.restrict_mono (show Ioc (0:ℝ≥0) a ⊆ Ioc 0 T from fun _ ht ↦ ⟨ht.1,ht.2.trans ha⟩) le_rfl) le_rfl
    have hh : (X b : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T a).prod μ] (q.X b) :=
      ae_of_ae_trim 𝓕.predictable_le_prod (restriction_ae (hWm i₀) ha (q.X b))
    exact hh.trans ((q.representative b).filter_mono (ae_mono hm))
  · intro b
    have he := CommonIntegralRestriction.restrict_equation hW hWm i₀ a T ha (ξ b)
      (driftInput T A B u q.X b) (fun i ↦ noiseInput T C D u q.X i b) (q.path b) (q.equation b)
    convert he using 1
    · exact (hec A B b).symm
    · funext i
      exact (hec (C i) (D i) b).symm

/-- The actual shifted solution retains its original endpoint as initial state,
its actual translated H² coordinates, and continuous S² paths. -/
def shifted (a δ T : ℝ≥0) (h : a+δ ≤ T)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (u : ν → H2 𝓕 μ T) (q : Solution hW hWm T A B C D ξ u) :
    Solution (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a)
      δ A B C D (fun b ↦ q.path b a) (fun b ↦ shiftCLM a δ T h (u b)) := by
  let X := fun b ↦ shiftCLM a δ T h (q.X b)
  let R := fun b t ↦ q.path b (a+t)
  have hp b : IsProgressive (CommonTimeShift.filtration 𝓕 a) (R b) :=
    CommonTimeShift.progressive (q.progressive b) a
  have hm : MapsTo (fun t ↦ a+t) (Iic δ) (Iic T) := fun _ ht ↦ (add_le_add le_rfl ht).trans h
  have hc b : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ R b t ω) (Iic δ) :=
    (q.continuous b).mono (fun _ hω ↦ hω.comp (continuous_const.add continuous_id).continuousOn hm)
  have hec (M : Matrix κ κ ℝ) (N : Matrix κ ν ℝ) (b : κ) :
      shiftCLM a δ T h (driftInput T M N u q.X b) =
      driftInput δ M N (fun c ↦ shiftCLM a δ T h (u c)) X b :=
    CommonPastedClasses.map_linearInput δ T
      (show H2 𝓕 μ T →L[ℝ] H2 (CommonTimeShift.filtration 𝓕 a) μ δ from shiftCLM a δ T h) M N q.X u b
  refine ⟨X,R,hp,hc,?_,?_,?_,?_⟩
  · intro b
    exact timeMap_S2 δ T (fun t ↦ a+t) (q.path b) hm (hp b) (q.continuous b) (hc b) (q.squareSup b)
  · intro b
    exact (shift_ae a δ T h (q.X b)).trans (pull_ae a δ T h (q.representative b))
  · intro b
    exact Filter.Eventually.of_forall (fun ω ↦ by change q.path b (a+0) ω = q.path b a ω; rw [add_zero])
  · intro b
    have he := CommonIntegralRestriction.shift_equation hW hWm a δ T h (ξ b)
      (driftInput T A B u q.X b) (fun i ↦ noiseInput T C D u q.X i b) (q.path b) (q.equation b)
    convert he using 1
    · exact (hec A B b).symm
    · funext i
      exact (hec (C i) (D i) b).symm
end LinearStochastic.CommonSolutionRestriction
