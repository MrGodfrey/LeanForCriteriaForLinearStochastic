import LinearStochastic.FilteredIto
import Mathlib

/-!
A constructed continuous stochastic integration map for one Gaussian increment,
on the complete L² subspace measurable for an arbitrary common past.
This is the L² closure of the one-interval adapted integral. It is not yet
continuous-time predictable-process integration on all time meshes.
-/
noncomputable section
namespace LinearStochastic.FilteredItoL2
open MeasureTheory ProbabilityTheory
open scoped NNReal
open LinearStochastic.StochasticFoundation

variable {Ω : Type*} (past : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  (Δ : Ω → ℝ) (v : ℝ≥0)
  (hlaw : HasLaw Δ (gaussianReal 0 v) P)
  (hfuture : Indep past (MeasurableSpace.comap Δ inferInstance) P)

local notation "A₂" => @lpMeas Ω ℝ ℝ _ _ _ past mΩ 2 P
local notation "L₂" => @Lp Ω ℝ mΩ _ 2 P

include hfuture in
/-- A.e. adapted representatives suffice; the original L² class is independent
of the increment, without choosing a pointwise-adapted representative as a new assumption. -/
theorem ae_adapted_independent {f : Ω → ℝ} (hf : AEStronglyMeasurable[past] f P) :
    IndepFun f Δ P := by
  letI : MeasurableSpace Ω := mΩ
  have hi := adapted_independent_increment past hfuture hf.stronglyMeasurable_mk.measurable
  exact hi.congr hf.ae_eq_mk.symm Filter.EventuallyEq.rfl

include hlaw hfuture

/-- The random product is truly L² even for a.e. adapted L² classes. -/
theorem product_memLp (f : A₂) :
    MemLp (fun ω ↦ f.val ω * Δ ω) 2 P := by
  letI : MeasurableSpace Ω := mΩ
  exact elementary_integral_memLp hlaw
    (ae_adapted_independent past Δ hfuture (lpMeas.aestronglyMeasurable f)) (Lp.memLp f.val)

def integral (f : A₂) : L₂ := by
  letI : MeasurableSpace Ω := mΩ
  exact (product_memLp past Δ v hlaw hfuture f).toLp (fun ω ↦ f.val ω * Δ ω)

theorem integral_coe (f : A₂) :
    ⇑(integral past Δ v hlaw hfuture f) =ᵐ[P] fun ω ↦ f.val ω * Δ ω :=
  MemLp.coeFn_toLp _

/-- Linearity is proved for the actual random-product L² equivalence classes. -/
def integralLinear : A₂ →ₗ[ℝ] L₂ := by
  letI : MeasurableSpace Ω := mΩ
  exact {
    toFun := integral past Δ v hlaw hfuture
    map_add' := fun f g ↦ by
      apply Lp.ext
      filter_upwards [integral_coe past Δ v hlaw hfuture (f+g),
        integral_coe past Δ v hlaw hfuture f, integral_coe past Δ v hlaw hfuture g,
        Lp.coeFn_add f.val g.val,
        Lp.coeFn_add (integral past Δ v hlaw hfuture f) (integral past Δ v hlaw hfuture g)]
        with ω hfg hf hg hc hs
      rw [hfg, hs]
      simp only [Pi.add_apply]
      rw [hf, hg]
      change ((f.val + g.val) ω) * Δ ω = _
      rw [hc]
      simp only [Pi.add_apply]
      ring
    map_smul' := fun c f ↦ by
      apply Lp.ext
      filter_upwards [integral_coe past Δ v hlaw hfuture (c • f),
        integral_coe past Δ v hlaw hfuture f, Lp.coeFn_smul c f.val,
        Lp.coeFn_smul c (integral past Δ v hlaw hfuture f)] with ω hcf hf hc hs
      change integral past Δ v hlaw hfuture (c • f) ω =
        (c • integral past Δ v hlaw hfuture f) ω
      rw [hcf, hs]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hf]
      change ((c • f.val) ω) * Δ ω = c * (f.val ω * Δ ω)
      rw [hc]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring }

omit hlaw hfuture in
theorem norm_sq_integral (f : L₂) : ‖f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂P := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial, ← pow_two]

theorem integral_norm_sq (f : A₂) :
    ‖integralLinear past Δ v hlaw hfuture f‖ ^ 2 = ‖f‖ ^ 2 * v := by
  letI : MeasurableSpace Ω := mΩ
  rw [norm_sq_integral]
  calc
    _ = ∫ ω, (f.val ω * Δ ω) ^ 2 ∂P :=
      integral_congr_ae ((integral_coe past Δ v hlaw hfuture f).mono fun ω hω ↦ by change (integral past Δ v hlaw hfuture f ω)^2 = _; rw [hω])
    _ = (∫ ω, f.val ω ^ 2 ∂P) * v := elementary_integral_isometry hlaw
      (ae_adapted_independent past Δ hfuture (lpMeas.aestronglyMeasurable f)) (Lp.memLp f.val)
    _ = ‖f‖ ^ 2 * v := by rw [← norm_sq_integral]; rfl

theorem integral_norm (f : A₂) :
    ‖integralLinear past Δ v hlaw hfuture f‖ = Real.sqrt v * ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f))).mp
  rw [integral_norm_sq, mul_pow, Real.sq_sqrt v.coe_nonneg]
  ring

/-- The actual bounded operator on the entire adapted L² subspace. -/
def integralCLM : A₂ →L[ℝ] L₂ :=
  (integralLinear past Δ v hlaw hfuture).mkContinuous (Real.sqrt v)
    (fun f ↦ (integral_norm past Δ v hlaw hfuture f).le)

/-- The normalized increment gives a constructed linear isometry. -/
def integralIsometry (hunit : HasLaw Δ (gaussianReal 0 1) P) :
    A₂ →ₗᵢ[ℝ] L₂ where
  toLinearMap := integralLinear past Δ 1 hunit hfuture
  norm_map' f := by simpa using integral_norm past Δ 1 hunit hfuture f

theorem integral_tendsto {α : Type*} {l : Filter α}
    {f : α → A₂} {g : A₂}
    (h : Filter.Tendsto f l (nhds g)) :
    Filter.Tendsto (fun a ↦ integral past Δ v hlaw hfuture (f a)) l
      (nhds (integral past Δ v hlaw hfuture g)) :=
  ((integralCLM past Δ v hlaw hfuture).continuous.tendsto g).comp h

omit hlaw hfuture in
/-- Simple random variables for the past, embedded through the genuine trim
isometry into the original probability-space L² subspace. -/
def adaptedSimple (hm : past ≤ mΩ) :
    @Lp.simpleFunc Ω ℝ past _ 2 (P.trim hm) → A₂ :=
  fun f ↦ (lpMeasToLpTrimLie ℝ ℝ 2 P hm).symm f.val

omit hlaw hfuture in
theorem adaptedSimple_dense (hm : past ≤ mΩ) :
    DenseRange (adaptedSimple past (P := P) hm) := by
  exact (lpMeasToLpTrimLie ℝ ℝ 2 P hm).symm.surjective.denseRange.comp
    (@Lp.simpleFunc.denseRange Ω ℝ past _ 2 (P.trim hm) _ (by norm_num : (2 : ENNReal) ≠ ⊤))
    (lpMeasToLpTrimLie ℝ ℝ 2 P hm).symm.continuous

omit hlaw in
/-- The normalized stochastic integral has a closed L² image. -/
theorem integralIsometry_closed_range (hm : past ≤ mΩ)
    (hunit : HasLaw Δ (gaussianReal 0 1) P) :
    IsClosed (Set.range (integralIsometry past Δ hfuture hunit)) := by
  letI : Fact (past ≤ mΩ) := ⟨hm⟩
  exact (integralIsometry past Δ hfuture hunit).isometry.isClosedEmbedding.isClosed_range

omit hlaw in
/-- Exact closure theorem: integrating all adapted L² variables is the L²
closure of the actual simple adapted integrals, for one normalized interval. -/
theorem integralIsometry_simple_closure (hm : past ≤ mΩ)
    (hunit : HasLaw Δ (gaussianReal 0 1) P) :
    closure (Set.range (fun f ↦ integralIsometry past Δ hfuture hunit
      (adaptedSimple past (P := P) hm f))) =
      Set.range (integralIsometry past Δ hfuture hunit) := by
  letI : Fact (past ≤ mΩ) := ⟨hm⟩
  have hc := (integralIsometry past Δ hfuture hunit).isometry.isClosedEmbedding
  change closure (Set.range ((integralIsometry past Δ hfuture hunit) ∘
    (adaptedSimple past (P := P) hm))) = _
  rw [Set.range_comp, hc.closure_image_eq, (adaptedSimple_dense past hm).closure_range,
    Set.image_univ]

end LinearStochastic.FilteredItoL2
