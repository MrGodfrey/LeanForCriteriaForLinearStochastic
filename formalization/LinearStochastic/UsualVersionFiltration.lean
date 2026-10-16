import LinearStochastic.JointUsualNatural
import LinearStochastic.CommonBrownianRepair

/-! The usual filtration is unchanged by actual process versions, on the same
complete probability space. This closes the filtration-identification part of
repairing Brownian paths; no informal replacement of the model is used. -/
noncomputable section
namespace LinearStochastic.UsualVersionFiltration
open MeasureTheory ProbabilityTheory CommonNullAugmentation
open scoped NNReal
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] [μ.IsComplete]
  {W V : ι → ℝ≥0 → Ω → ℝ}
  (hWm : ∀ i t, Measurable (W i t)) (hVm : ∀ i t, Measurable (V i t))

omit [Fintype ι] [IsProbabilityMeasure μ] [μ.IsComplete] in
/-- A complete filtration containing one version contains the original process
at every time, using its actual natural-filtration generators. -/
theorem natural_le_of_ae {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
    (hV : ∀ i t, Measurable[𝓕 t] (V i t))
    (he : ∀ i t, W i t =ᵐ[μ] V i t) :
    JointCylinderGeneration.natural W hWm ≤ 𝓕 := by
  intro T
  rw [JointCylinderGeneration.natural_eq]
  apply iSup_le
  intro i
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  exact ((CommonFiltrationCompletion.measurable_of_ae_eq 𝓕 t (hV i t) (he i t)).mono
    (𝓕.mono ht) le_rfl).comap_le

omit [Fintype ι] [IsProbabilityMeasure μ] [μ.IsComplete] in
/-- The actual usual augmentation is the smallest complete right-continuous
filtration containing the actual natural filtration. -/
theorem usual_le {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ] [𝓕.IsRightContinuous]
    (h : JointCylinderGeneration.natural W hWm ≤ 𝓕) :
    JointUsualNatural.usual (μ:=μ) W hWm ≤ 𝓕 := by
  have ha : JointUsualNatural.augmented (μ:=μ) W hWm ≤ 𝓕 :=
    sup_le h (fun t ↦ CommonFiltrationCompletion.nullsAlg_le_complete 𝓕 t)
  intro t
  have hh : JointUsualNatural.usual (μ:=μ) W hWm t ≤ 𝓕.rightCont t := by
    change (JointUsualNatural.augmented (μ:=μ) W hWm).rightCont t ≤ 𝓕.rightCont t
    rw [Filtration.rightCont_eq,Filtration.rightCont_eq]
    exact iInf_mono fun s ↦ iInf_mono fun _ ↦ ha s
  rwa [Filtration.IsRightContinuous.eq] at hh

omit [Fintype ι] [IsProbabilityMeasure μ] [μ.IsComplete] in
/-- Whole-future independence and adaptation transfer across a genuine common
path version on a complete filtration, in either direction. -/
theorem forward_congr {B C : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    [𝓕.IsComplete μ] [hB : CommonItoIsometry.ForwardIndependent B 𝓕 μ]
    (he : ∀ᵐ ω ∂μ, ∀ t, B t ω = C t ω) :
    CommonItoIsometry.ForwardIndependent C 𝓕 μ where
  adapted t := (CommonFiltrationCompletion.measurable_of_ae_eq 𝓕 t (hB.adapted t).measurable
    (he.mono fun ω hω ↦ (hω t).symm)).stronglyMeasurable
  indep s := by
    apply CommonFiltrationCompletion.indep_comap_congr _ (hB.indep s)
    filter_upwards [he] with ω hω
    funext u
    rw [hω (s+u),hω s]

omit [Fintype ι] [IsProbabilityMeasure μ] [μ.IsComplete] in
/-- Joint future independence also transfers across actual process versions. -/
theorem pairForward_congr {B C D E : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
    (hp : CommonItoCross.PairForwardIndependent B C 𝓕 μ)
    (hBD : ∀ᵐ ω ∂μ, ∀ t, B t ω = D t ω)
    (hCE : ∀ᵐ ω ∂μ, ∀ t, C t ω = E t ω) :
    CommonItoCross.PairForwardIndependent D E 𝓕 μ := by
  intro s
  apply CommonFiltrationCompletion.indep_comap_congr _ (hp s)
  filter_upwards [hBD,hCE] with ω hB hC
  apply Prod.ext <;> funext u
  · change B (s+u) ω-B s ω = D (s+u) ω-D s ω
    rw [hB (s+u),hB s]
  · change C (s+u) ω-C s ω = E (s+u) ω-E s ω
    rw [hC (s+u),hC s]

/-- Equality of actual usual filtrations under timewise almost-everywhere
versions. No pathwise measurability or right-continuation equality is assumed. -/
theorem usual_eq_of_ae (he : ∀ i t, W i t =ᵐ[μ] V i t) :
    JointUsualNatural.usual (μ:=μ) W hWm = JointUsualNatural.usual (μ:=μ) V hVm := by
  apply le_antisymm
  · apply usual_le hWm
    apply natural_le_of_ae hWm _ he
    intro i t
    exact (JointCylinderGeneration.measurable_natural V hVm i le_rfl).mono
      (JointUsualNatural.natural_le_usual V hVm t) le_rfl
  · apply usual_le hVm
    apply natural_le_of_ae hVm _ (fun i t ↦ (he i t).symm)
    intro i t
    exact (JointCylinderGeneration.measurable_natural W hWm i le_rfl).mono
      (JointUsualNatural.natural_le_usual W hWm t) le_rfl

/-- Brownian simultaneous path repair preserves precisely the paper's usual
augmentation of the joint natural filtration on the original probability space. -/
theorem repaired_usual_eq (hW : ∀ i, IsBrownianReal (W i) μ) :
    JointUsualNatural.usual (μ:=μ) W hWm =
      JointUsualNatural.usual (μ:=μ) (CommonBrownianRepair.repaired hW)
        (CommonBrownianRepair.repaired_measurable hW) := by
  apply usual_eq_of_ae hWm (CommonBrownianRepair.repaired_measurable hW)
  intro i t
  filter_upwards [(hW i).mk_ae_forall_eq] with ω hω
  exact (hω t).symm

end LinearStochastic.UsualVersionFiltration
