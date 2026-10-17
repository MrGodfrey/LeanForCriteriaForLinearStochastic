module

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

The rectangle-splitting argument is adapted from ItoIsometryAdapted.lean at
formal-applied-math/formal-mathfin 99b836298731c432a6242fdb6cb51c1c97f37902.
Here two distinct Brownian channels replace the repeated scalar driver, and
actual joint forward independence and independent path laws give zero pairing.
The two-variable dense extension and multichannel interface are local additions.
-/
public import LinearStochastic.CommonItoCLM

@[expose] public section

noncomputable section
namespace LinearStochastic.CommonItoCross
open MeasureTheory ProbabilityTheory CommonItoIsometry CommonItoL2 CommonItoCLM
open scoped NNReal ENNReal InnerProductSpace
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {B C : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [hFB : ForwardIndependent B 𝓕 μ] [hFC : ForwardIndependent C 𝓕 μ]
  (hB : IsPreBrownianReal B μ) (hC : IsPreBrownianReal C μ)

/-- Actual joint future independence, containing no integral conclusion. -/
def PairForwardIndependent (B C : ℝ≥0 → Ω → ℝ) (𝓕 : Filtration ℝ≥0 mΩ)
    (μ : Measure Ω) : Prop := ∀ s, Indep (𝓕 s)
      (MeasurableSpace.comap (fun ω ↦
        ((fun u ↦ B (s+u) ω - B s ω), (fun u ↦ C (s+u) ω - C s ω))) inferInstance) μ

theorem PairForwardIndependent.symm (h : PairForwardIndependent B C 𝓕 μ) :
    PairForwardIndependent C B 𝓕 μ := by
  intro s
  exact indep_of_indep_of_le_right (h s)
    (((measurable_snd.prodMk measurable_fst).comp
      (comap_measurable (fun ω ↦
        ((fun u ↦ B (s+u) ω - B s ω), (fun u ↦ C (s+u) ω - C s ω))))).comap_le)

theorem adapted_indepFun_pair (hp : PairForwardIndependent B C 𝓕 μ)
    {s : ℝ≥0} {φ : Ω → ℝ} (hφ : AdaptedAt 𝓕 s φ)
    {H : (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ} (hH : Measurable H) :
    IndepFun φ (fun ω ↦ H ((fun u ↦ B (s+u) ω - B s ω),
      (fun u ↦ C (s+u) ω - C s ω))) μ := by
  have h := indep_of_indep_of_le_left (hp s) (measurable_iff_comap_le.mp hφ)
  have hi : IndepFun φ (fun ω ↦ ((fun u ↦ B (s+u) ω - B s ω),
      (fun u ↦ C (s+u) ω - C s ω))) μ := h
  exact hi.comp measurable_id hH

include hB hC

/-- Independent actual Brownian paths have zero mixed increment covariance. -/
theorem integral_cross_increment
    (hBC : IndepFun (fun ω t ↦ B t ω) (fun ω t ↦ C t ω) μ)
    (hBm : ∀ t, Measurable (B t)) (hCm : ∀ t, Measurable (C t))
    (a b c d : ℝ≥0) :
    ∫ ω, (B b ω-B a ω) * (C d ω-C c ω) ∂μ = 0 := by
  have hi := hBC.comp ((measurable_pi_apply b).sub (measurable_pi_apply a))
    ((measurable_pi_apply d).sub (measurable_pi_apply c))
  change IndepFun (fun ω ↦ B b ω - B a ω) (fun ω ↦ C d ω - C c ω) μ at hi
  rw [hi.integral_fun_mul_eq_mul_integral
    ((hBm b).sub (hBm a)).aestronglyMeasurable
    ((hCm d).sub (hCm c)).aestronglyMeasurable]
  have hz : ∫ ω, B b ω-B a ω ∂μ = 0 := by
    have h := (hB.hasLaw_sub b a).integral_eq
    rwa [integral_id_gaussianReal] at h
  rw [hz, zero_mul]

lemma integrable_bdd_cross_increment
    {f : Ω → ℝ} (hf : Measurable f) {K : ℝ} (hfb : ∀ ω, |f ω| ≤ K)
    (a b c d : ℝ≥0) :
    Integrable (fun ω ↦ f ω * ((B b ω-B a ω)*(C d ω-C c ω))) μ := by
  have hi : Integrable (fun ω ↦ (B b ω-B a ω)*(C d ω-C c ω)) μ :=
    (hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two).integrable_mul
      (hC.isGaussianProcess.hasGaussianLaw_sub.memLp_two)
  exact hi.bdd_mul hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs];exact hfb ω)

/-- Cross-channel rectangle pairing, including overlapping time intervals. -/
lemma rect_cross_pairing_aux
    (hp : PairForwardIndependent B C 𝓕 μ)
    (hBC : IndepFun (fun ω t ↦ B t ω) (fun ω t ↦ C t ω) μ)
    (hBm : ∀ t, Measurable (B t)) (hCm : ∀ t, Measurable (C t))
    {f g : Ω → ℝ} {s t s' t' : ℝ≥0}
    (hf : AdaptedAt 𝓕 s f) (hg : AdaptedAt 𝓕 s' g)
    {Cf Cg : ℝ} (hfb : ∀ ω, |f ω| ≤ Cf) (hgb : ∀ ω, |g ω| ≤ Cg)
    (_hst : s ≤ t) (hst' : s' ≤ t') (hss' : s ≤ s') :
    ∫ ω, (f ω*(B t ω-B s ω))*(g ω*(C t' ω-C s' ω)) ∂μ = 0 := by
  have hfg : AdaptedAt 𝓕 s' (fun ω ↦ f ω*g ω) := (hf.mono hss').mul hg
  have hfgm : Measurable (fun ω ↦ f ω*g ω) := (hf.measurable hBm).mul (hg.measurable hCm)
  have hfgb : ∀ ω, |f ω*g ω| ≤ Cf*Cg := fun ω ↦ by
    rw [abs_mul]
    exact mul_le_mul (hfb ω) (hgb ω) (abs_nonneg _) ((abs_nonneg _).trans (hfb ω))
  by_cases htle : t ≤ s'
  · have hχ : AdaptedAt 𝓕 s' (fun ω ↦ f ω*(B t ω-B s ω)*g ω) :=
      ((hf.mono hss').mul ((adaptedAt_eval (μ:=μ) htle).sub
        (adaptedAt_eval (μ:=μ) hss'))).mul hg
    have hz := integral_adapted_mul_increment hC hCm hst' hχ
    rw [← hz]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
  · replace htle := (not_le.mp htle).le
    have hT1 : ∫ ω, f ω*g ω*((B s' ω-B s ω)*(C t' ω-C s' ω)) ∂μ = 0 := by
      have hχ : AdaptedAt 𝓕 s' (fun ω ↦ f ω*g ω*(B s' ω-B s ω)) :=
        hfg.mul ((adaptedAt_eval (μ:=μ) (𝓕:=𝓕) le_rfl).sub
          (adaptedAt_eval (μ:=μ) hss'))
      have hz := integral_adapted_mul_increment hC hCm hst' hχ
      rw [← hz]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
    have hi : IndepFun (fun ω ↦ f ω*g ω)
        (fun ω ↦ (B t ω-B s' ω)*(C t' ω-C s' ω)) μ := by
      have hm : Measurable (fun p : (ℝ≥0→ℝ)×(ℝ≥0→ℝ) ↦ p.1 (t-s')*p.2 (t'-s')) := by fun_prop
      have hh := adapted_indepFun_pair hp hfg hm
      simpa only [add_tsub_cancel_of_le htle, add_tsub_cancel_of_le hst'] using hh
    have hT2 : ∫ ω, f ω*g ω*((B t ω-B s' ω)*(C t' ω-C s' ω)) ∂μ = 0 := by
      rw [hi.integral_fun_mul_eq_mul_integral hfgm.aestronglyMeasurable
        (((hBm t).sub (hBm s')).mul ((hCm t').sub (hCm s'))).aestronglyMeasurable,
        integral_cross_increment hB hC hBC hBm hCm, mul_zero]
    have heq : (∫ ω, (f ω*(B t ω-B s ω))*(g ω*(C t' ω-C s' ω)) ∂μ) =
        (∫ ω, f ω*g ω*((B s' ω-B s ω)*(C t' ω-C s' ω)) ∂μ) +
        (∫ ω, f ω*g ω*((B t ω-B s' ω)*(C t' ω-C s' ω)) ∂μ) := by
      rw [← integral_add (integrable_bdd_cross_increment hB hC hfgm hfgb s s' s' t')
        (integrable_bdd_cross_increment hB hC hfgm hfgb s' t s' t')]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
    rw [heq,hT1,hT2,zero_add]

theorem rect_cross_pairing
    (hp : PairForwardIndependent B C 𝓕 μ)
    (hBC : IndepFun (fun ω t ↦ B t ω) (fun ω t ↦ C t ω) μ)
    (hBm : ∀ t, Measurable (B t)) (hCm : ∀ t, Measurable (C t))
    {f g : Ω → ℝ} {s t s' t' : ℝ≥0}
    (hf : AdaptedAt 𝓕 s f) (hg : AdaptedAt 𝓕 s' g)
    {Cf Cg : ℝ} (hfb : ∀ ω, |f ω| ≤ Cf) (hgb : ∀ ω, |g ω| ≤ Cg)
    (hst : s ≤ t) (hst' : s' ≤ t') :
    ∫ ω, (f ω*(B t ω-B s ω))*(g ω*(C t' ω-C s' ω)) ∂μ = 0 := by
  rcases le_total s s' with hh|hh
  · exact rect_cross_pairing_aux hB hC hp hBC hBm hCm hf hg hfb hgb hst hst' hh
  · have hz := rect_cross_pairing_aux hC hB hp.symm hBC.symm hCm hBm hg hf hgb hfb hst' hst hh
    rw [← hz]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)



/-- The actual increment sums for two channels are orthogonal. -/
theorem itoSimple_cross_integral
    (hp : PairForwardIndependent B C 𝓕 μ)
    (hBC : IndepFun (fun ω t ↦ B t ω) (fun ω t ↦ C t ω) μ)
    (hBm : ∀ t, Measurable (B t)) (hCm : ∀ t, Measurable (C t))
    (V W : SimpleProcess ℝ 𝓕) :
    ∫ ω, itoSimple hBm V ω * itoSimple hCm W ω ∂μ = 0 := by
  let a : (ℝ≥0 × ℝ≥0) → Ω → ℝ := fun p ω ↦ V.value p ω * (B p.2 ω-B p.1 ω)
  let b : (ℝ≥0 × ℝ≥0) → Ω → ℝ := fun p ω ↦ W.value p ω * (C p.2 ω-C p.1 ω)
  have ha : ∀ p ∈ V.value.support, MemLp (a p) 2 μ := fun p hp ↦
    memLp_adapted_mul_increment hB hBm (V.le_of_mem_support_value p hp)
      (V.measurable_value p) (MemLp.of_bound
        ((V.measurable_value p).mono (𝓕.le p.1) le_rfl).aestronglyMeasurable
        V.valueBound (ae_of_all _ (V.value_le_valueBound p)))
  have hb : ∀ p ∈ W.value.support, MemLp (b p) 2 μ := fun p hp ↦
    memLp_adapted_mul_increment hC hCm (W.le_of_mem_support_value p hp)
      (W.measurable_value p) (MemLp.of_bound
        ((W.measurable_value p).mono (𝓕.le p.1) le_rfl).aestronglyMeasurable
        W.valueBound (ae_of_all _ (W.value_le_valueBound p)))
  have hi : ∀ p ∈ V.value.support, ∀ q ∈ W.value.support,
      Integrable (fun ω ↦ a p ω*b q ω) μ :=
    fun p hp q hq ↦ (ha p hp).integrable_mul (hb q hq)
  calc
    (∫ ω, itoSimple hBm V ω * itoSimple hCm W ω ∂μ) =
        ∫ ω, ∑ p ∈ V.value.support, ∑ q ∈ W.value.support, a p ω * b q ω ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      change (∑ p ∈ V.value.support, a p ω)*(∑ q ∈ W.value.support, b q ω) = _
      exact Finset.sum_mul_sum _ _ _ _
    _ = ∑ p ∈ V.value.support, ∑ q ∈ W.value.support,
        ∫ ω, a p ω * b q ω ∂μ := by
      rw [integral_finsetSum _ (fun p hp ↦ integrable_finsetSum _ fun q hq ↦ hi p hp q hq)]
      exact Finset.sum_congr rfl fun p hp ↦ integral_finsetSum _ (fun q hq ↦ hi p hp q hq)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro p hpV
      apply Finset.sum_eq_zero
      intro q hqW
      exact rect_cross_pairing hB hC hp hBC hBm hCm
        (V.measurable_value p) (W.measurable_value q)
        (fun ω ↦ by rw [← Real.norm_eq_abs];exact V.value_le_valueBound p ω)
        (fun ω ↦ by rw [← Real.norm_eq_abs];exact W.value_le_valueBound q ω)
        (V.le_of_mem_support_value p hpV) (W.le_of_mem_support_value q hqW)

theorem itoSimpleLp_cross_inner
    (hp : PairForwardIndependent B C 𝓕 μ)
    (hBC : IndepFun (fun ω t ↦ B t ω) (fun ω t ↦ C t ω) μ)
    (hBm : ∀ t, Measurable (B t)) (hCm : ∀ t, Measurable (C t))
    (V W : SimpleProcess ℝ 𝓕) :
    ⟪itoSimpleLp hB hBm V, itoSimpleLp hC hCm W⟫_ℝ = 0 := by
  rw [L2.inner_def, ← itoSimple_cross_integral hB hC hp hBC hBm hCm V W]
  apply integral_congr_ae
  filter_upwards [(memLp_itoSimple hB hBm V).coeFn_toLp,
    (memLp_itoSimple hC hCm W).coeFn_toLp] with ω hV hW
  change (itoSimpleLp hC hCm W : Ω → ℝ) ω * (itoSimpleLp hB hBm V : Ω → ℝ) ω = _
  change (itoSimpleLp hB hBm V : Ω → ℝ) ω = _ at hV
  change (itoSimpleLp hC hCm W : Ω → ℝ) ω = _ at hW
  rw [hV,hW,mul_comm]

/-- Orthogonality survives the actual dense continuous extension for arbitrary
common-predictable spacetime L² integrands, with no fixed partition. -/
theorem itoIntegral_cross_inner
    (hp : PairForwardIndependent B C 𝓕 μ)
    (hBC : IndepFun (fun ω t ↦ B t ω) (fun ω t ↦ C t ω) μ)
    (hBm : ∀ t, Measurable (B t)) (hCm : ∀ t, Measurable (C t)) (T : ℝ≥0)
    (f g : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm)) :
    ⟪itoIntegralCLM_T (𝓕:=𝓕) hB T hBm f,
      itoIntegralCLM_T (𝓕:=𝓕) hC T hCm g⟫_ℝ = 0 := by
  have hs (V : TBoundedSP (𝓕:=𝓕) T hBm) :
      ∀ g : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm),
      ⟪itoIntegralCLM_T (𝓕:=𝓕) hB T hBm (simpleAssembly_T (𝓕:=𝓕) T hBm V),
        itoIntegralCLM_T (𝓕:=𝓕) hC T hCm g⟫_ℝ = 0 := by
    intro g
    refine congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (𝓕:=𝓕) (μ:=μ) T hCm)
      (continuous_const.inner (itoIntegralCLM_T (𝓕:=𝓕) hC T hCm).continuous)
      continuous_const ?_) g
    funext W
    rw [Function.comp_apply, Function.comp_apply, itoIntegralCLM_T_simpleAssembly_T,
      itoIntegralCLM_T_simpleAssembly_T]
    exact itoSimpleLp_cross_inner hB hC hp hBC hBm hCm V.val W.val
  refine congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (𝓕:=𝓕) (μ:=μ) T hBm)
    ((itoIntegralCLM_T (𝓕:=𝓕) hB T hBm).continuous.inner continuous_const)
    continuous_const ?_) f
  funext V
  exact hs V g

end LinearStochastic.CommonItoCross
