/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
Generic monoMeasureLp and its representative proof adapted verbatim from
MathFin/Foundations/ItoIntegralProcessL2Infinite.lean at
99b836298731c432a6242fdb6cb51c1c97f37902. Remaining finite-horizon compatibility
uses the actual common-filtration clamp proof.
-/
import LinearStochastic.CommonHorizonClamp

set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonHorizonRestriction
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open CommonItoL2 CommonItoCLM CommonItoProcess CommonItoProcessGeneral CommonHorizonClamp
section MonoMeasureLp
variable {α : Type*} {_mα : MeasurableSpace α} {μ ν : Measure α}

/-- **The `Lp` inclusion for `ν ≤ μ`.** For `f ∈ Lp 2 μ` the *same* function lies in
`Lp 2 ν` with no larger norm (a smaller measure can only shrink the `L²` norm), so
`f ↦ f` is a norm-`≤ 1` continuous linear map `Lp 2 μ →L[ℝ] Lp 2 ν`. Mathlib has
`MemLp.mono_measure` but no packaged CLM; generic measure theory, a natural upstream
candidate. Specialises to measure restriction (`ν = μ.restrict s`, via
`Measure.restrict_le_self`). -/
noncomputable def monoMeasureLp (h : ν ≤ μ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
  LinearMap.mkContinuous
    { toFun := fun f ↦ ((Lp.memLp f).mono_measure h).toLp
      map_add' := fun f g ↦ by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).mono_measure h),
          Lp.coeFn_add (((Lp.memLp f).mono_measure h).toLp) (((Lp.memLp g).mono_measure h).toLp),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_measure h),
          MemLp.coeFn_toLp ((Lp.memLp g).mono_measure h),
          (Lp.coeFn_add f g).filter_mono (ae_mono h)] with x h1 h2 h3 h4 h5
        simp only [h1, h2, h3, h4, h5, Pi.add_apply]
      map_smul' := fun c f ↦ by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).mono_measure h),
          Lp.coeFn_smul c (((Lp.memLp f).mono_measure h).toLp),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_measure h),
          (Lp.coeFn_smul c f).filter_mono (ae_mono h)] with x h1 h2 h3 h4
        simp only [h1, h2, h3, h4, Pi.smul_apply, RingHom.id_apply] }
    1 (fun f ↦ by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul, Lp.norm_def]
      refine ENNReal.toReal_mono (Lp.memLp f).2.ne ?_
      rw [eLpNorm_congr_ae (MemLp.coeFn_toLp ((Lp.memLp f).mono_measure h))]
      exact eLpNorm_mono_measure _ h)

@[simp] lemma monoMeasureLp_coeFn (h : ν ≤ μ) (f : Lp ℝ 2 μ) :
    ⇑(monoMeasureLp h f) =ᵐ[ν] ⇑f := by
  simp only [monoMeasureLp, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  exact MemLp.coeFn_toLp _

end MonoMeasureLp

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent B 𝓕 μ]
  (hB : IsPreBrownianReal B μ) (hBm : ∀ t, Measurable (B t))

/-- True monotonicity of the predictable trimmed horizon measures. -/
theorem measure_le {t T : ℝ≥0} (h : t ≤ T) :
    trimMeasure_T (𝓕:=𝓕) (μ:=μ) t hBm ≤ trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm := by
  rw [trimMeasure_T_eq_restrict,trimMeasure_T_eq_restrict]
  apply Measure.restrict_mono _ le_rfl
  intro z hz
  exact ⟨⟨hz.1.1,hz.1.2.trans h⟩,hz.2⟩

/-- Actual restriction on the same common filtration, represented by identity. -/
def restriction {t T : ℝ≥0} (h : t ≤ T) :
    Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm) →L[ℝ]
      Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) t hBm) := monoMeasureLp (measure_le hBm h)

theorem restriction_ae {t T : ℝ≥0} (h : t ≤ T)
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm)) :
    restriction hBm h f =ᵐ[trimMeasure_T (𝓕:=𝓕) (μ:=μ) t hBm] f := monoMeasureLp_coeFn _ f

theorem restriction_simple {t T : ℝ≥0} (h : t ≤ T)
    (V : TBoundedSP (𝓕:=𝓕) T hBm) :
    restriction hBm h (simpleAssembly_T (𝓕:=𝓕) (μ:=μ) T hBm V) =
      simpleProcessL2_T (𝓕:=𝓕) (μ:=μ) t hBm V.val := by
  apply Lp.ext
  exact (restriction_ae hBm h _).trans
    (((memLp_uncurry_trim_T (𝓕:=𝓕) (μ:=μ) T hBm V.val).coeFn_toLp.filter_mono
      (ae_mono (measure_le hBm h))).trans
      (memLp_uncurry_trim_T (𝓕:=𝓕) (μ:=μ) t hBm V.val).coeFn_toLp.symm)

/-- The actual stochastic process value does not depend on a later choice of
integrand horizon. Equality is proved on clamped simple sums and by density. -/
theorem process_restriction {s t T : ℝ≥0} (hs : s ≤ t) (h : t ≤ T)
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm)) :
    itoProcessCLM (𝓕:=𝓕) hB t s hBm (restriction hBm h f) =
      itoProcessCLM (𝓕:=𝓕) hB T s hBm f := by
  refine (simpleAssembly_T_denseRange (𝓕:=𝓕) (μ:=μ) T hBm).induction_on f
    (isClosed_eq ((itoProcessCLM (𝓕:=𝓕) hB t s hBm).continuous.comp
      (restriction (𝓕:=𝓕) (μ:=μ) hBm h).continuous)
      (itoProcessCLM (𝓕:=𝓕) hB T s hBm).continuous) ?_
  intro V
  rw [restriction_simple hBm h V,itoProcessCLM_simpleAssembly_T]
  apply Lp.ext
  exact (itoProcessCLM_simpleProcessL2_T hB t s hBm V.val hs).trans
    (memLp_itoSimpleProcess hB hBm V.val s).coeFn_toLp.symm

theorem terminal_restriction {t T : ℝ≥0} (h : t ≤ T)
    (f : Lp ℝ 2 (trimMeasure_T (𝓕:=𝓕) (μ:=μ) T hBm)) :
    itoIntegralCLM_T (𝓕:=𝓕) hB t hBm (restriction hBm h f) =
      itoProcessCLM (𝓕:=𝓕) hB T t hBm f := by
  rw [←itoProcessCLM_terminal_eq]
  exact process_restriction hB hBm le_rfl h f
end LinearStochastic.CommonHorizonRestriction
