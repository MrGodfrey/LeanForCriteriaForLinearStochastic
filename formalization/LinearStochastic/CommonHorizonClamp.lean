module

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
Adapted from MathFin/Foundations/ItoIntegralProcessL2Infinite.lean at
99b836298731c432a6242fdb6cb51c1c97f37902: actual clamp definitions and proofs
with the arbitrary specified common filtration; both helper proofs made public.
-/
public import LinearStochastic.CommonItoProcessGeneral

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonHorizonClamp
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
open CommonItoL2 CommonItoCLM CommonItoProcess CommonItoProcessGeneral
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent B 𝓕 μ]
  (hB : IsPreBrownianReal B μ)
/-- Fiber-sum value of the clamped `mapDomain`: `mapDomain` collapses intervals sharing a
left endpoint, so the value at `p` is the (finite) sum of the original `V`-values over the
clamp-preimage of `p`. The contributors all share `p`'s left endpoint, which keeps the
value `𝓕_{p.1}`-measurable. -/
lemma clamp_value_apply (T : ℝ≥0)
    (V : SimpleProcess ℝ 𝓕) (p : ℝ≥0 × ℝ≥0) (ω : Ω) :
    ((V.value.filter (fun q ↦ q.1 ≤ T)).mapDomain (fun q ↦ (q.1, q.2 ⊓ T))) p ω
      = ∑ a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support,
          (if (a.1, a.2 ⊓ T) = p then V.value a ω else 0) := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  rw [Finsupp.support_filter, Finset.mem_filter] at ha
  rw [Finsupp.single_apply]
  by_cases h : (a.1, a.2 ⊓ T) = p
  · simp only [if_pos h, Finsupp.filter_apply_pos (fun q ↦ q.1 ≤ T) V.value ha.2]
  · simp only [if_neg h, Pi.zero_apply]

/-- **The `[0,T]` clamp of a simple process.** -/
noncomputable def clampSP (T : ℝ≥0) (_hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ 𝓕) :
    SimpleProcess ℝ 𝓕 where
  valueBot := V.valueBot
  value := (V.value.filter (fun q ↦ q.1 ≤ T)).mapDomain (fun q ↦ (q.1, q.2 ⊓ T))
  le_of_mem_support_value := fun p hp ↦ by
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hp)
    rw [Finsupp.support_filter, Finset.mem_filter] at ha
    exact le_inf (V.le_of_mem_support_value a ha.1) ha.2
  measurable_valueBot := V.measurable_valueBot
  measurable_value' := fun p hp ↦ by
    rw [show ((V.value.filter (fun q ↦ q.1 ≤ T)).mapDomain (fun q ↦ (q.1, q.2 ⊓ T))) p
          = fun ω ↦ ∑ a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support,
              (if (a.1, a.2 ⊓ T) = p then V.value a ω else 0)
        from funext fun ω ↦ clamp_value_apply T V p ω]
    refine Finset.measurable_sum _ fun a ha ↦ ?_
    by_cases h : (a.1, a.2 ⊓ T) = p
    · simp only [if_pos h]
      rw [Finsupp.support_filter, Finset.mem_filter] at ha
      have hp1 : a.1 = p.1 := (Prod.ext_iff.mp h).1
      exact hp1 ▸ V.measurable_value a
    · simp only [if_neg h]; exact measurable_const
  bounded_valueBot := V.bounded_valueBot
  bounded_value := by
    refine ⟨(V.value.filter (fun q ↦ q.1 ≤ T)).support.card • |V.valueBound|, fun p hp ω ↦ ?_⟩
    rw [clamp_value_apply T V p ω]
    calc ‖∑ a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support,
              (if (a.1, a.2 ⊓ T) = p then V.value a ω else 0)‖
        ≤ ∑ a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support,
            ‖(if (a.1, a.2 ⊓ T) = p then V.value a ω else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ (V.value.filter (fun q ↦ q.1 ≤ T)).support, |V.valueBound| := by
          refine Finset.sum_le_sum fun a ha ↦ ?_
          by_cases h : (a.1, a.2 ⊓ T) = p
          · simp only [if_pos h]
            exact (V.value_le_valueBound a ω).trans (le_abs_self _)
          · simp only [if_neg h, norm_zero]; exact abs_nonneg _
      _ = (V.value.filter (fun q ↦ q.1 ≤ T)).support.card • |V.valueBound| := by
          rw [Finset.sum_const]

/-- **Master `Finsupp.sum` identity for the clamp.** Any additive-in-the-value statistic
`φ` summed over the clamp equals the same statistic summed over `V`, provided `φ` is
invariant under the right-endpoint clamp on the kept intervals (`hclamp`) and vanishes on
the dropped ones (`hdrop`). Both `clampSP_itoSimpleProcess` and `clampSP_simpleProcessL2_T`
are instances. -/
lemma clampSP_value_sum {N : Type*} [AddCommMonoid N] (T : ℝ≥0)
    (hBmeas : ∀ u, Measurable (B u)) (V : SimpleProcess ℝ 𝓕)
    (φ : ℝ≥0 × ℝ≥0 → (Ω → ℝ) → N)
    (hφ0 : ∀ p, φ p 0 = 0) (hφadd : ∀ p u v, φ p (u + v) = φ p u + φ p v)
    (hclamp : ∀ a ∈ V.value.support, a.1 ≤ T → φ (a.1, a.2 ⊓ T) (V.value a) = φ a (V.value a))
    (hdrop : ∀ a ∈ V.value.support, T < a.1 → φ a (V.value a) = 0) :
    (clampSP T hBmeas V).value.sum φ = V.value.sum φ := by
  show ((V.value.filter (fun q ↦ q.1 ≤ T)).mapDomain (fun q ↦ (q.1, q.2 ⊓ T))).sum φ
      = V.value.sum φ
  rw [Finsupp.sum_mapDomain_index hφ0 hφadd, Finsupp.sum, Finsupp.support_filter,
      Finset.sum_filter]
  conv_rhs => rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun a ha ↦ ?_
  by_cases hP : a.1 ≤ T
  · rw [if_pos hP, Finsupp.filter_apply_pos (fun q ↦ q.1 ≤ T) V.value hP]
    exact hclamp a ha hP
  · rw [if_neg hP]
    exact (hdrop a ha (not_le.mp hP)).symm

/-- **Clamp preserves the `[0,t]` discrete Itô integral for `t ≤ T`.** -/
lemma clampSP_itoSimpleProcess (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ 𝓕) (ht : t ≤ T) :
    itoSimpleProcess hBmeas (clampSP T hBmeas V) t = itoSimpleProcess hBmeas V t := by
  funext ω
  rw [itoSimpleProcess_apply, itoSimpleProcess_apply]
  refine clampSP_value_sum T hBmeas V (fun p v ↦ v ω * (B (min p.2 t) ω - B (min p.1 t) ω))
    (fun p ↦ by simp) (fun p u v ↦ by simp only [Pi.add_apply]; ring)
    (fun a ha hP ↦ ?_) (fun a ha hP ↦ ?_)
  · rw [show min (a.2 ⊓ T) t = min a.2 t from by rw [min_assoc, min_eq_right ht]]
  · have h1 : min a.1 t = t := min_eq_right (le_of_lt (lt_of_le_of_lt ht hP))
    have h2 : min a.2 t = t :=
      min_eq_right (le_of_lt (lt_of_le_of_lt ht (lt_of_lt_of_le hP (V.le_of_mem_support_value a ha))))
    rw [h1, h2, sub_self, mul_zero]

/-- **Clamp agrees with `V` pointwise on the band `(0,T]`.** -/
lemma clampSP_apply (T s : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ 𝓕) (hsT : s ≤ T) (ω : Ω) :
    (clampSP T hBmeas V) s ω = V s ω := by
  rw [SimpleProcess.apply_eq, SimpleProcess.apply_eq]
  congr 1
  exact clampSP_value_sum T hBmeas V (fun p v ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) s)
    (fun p ↦ by simp)
    (fun p u v ↦ by
      simp only [Set.indicator_apply, Pi.add_apply]
      split_ifs <;> simp)
    (fun a ha hP ↦ by
      simp only [Set.indicator_apply]
      refine if_congr (Iff.intro (fun h ↦ ⟨h.1, h.2.trans inf_le_left⟩)
        (fun h ↦ ⟨h.1, le_inf h.2 hsT⟩)) rfl rfl)
    (fun a ha hP ↦ by
      rw [Set.indicator_of_notMem]
      rintro ⟨h1, _⟩
      exact absurd (lt_of_le_of_lt hsT hP) (not_lt.mpr h1.le))

/-- **Clamp preserves the `[0,T]` `L²` integrand.** -/
lemma clampSP_simpleProcessL2_T (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ 𝓕) :
    simpleProcessL2_T (μ := μ) T hBmeas (clampSP T hBmeas V)
      = simpleProcessL2_T (μ := μ) T hBmeas V := by
  refine Lp.ext ((MemLp.coeFn_toLp (memLp_uncurry_trim_T T hBmeas (clampSP T hBmeas V))).trans
    ((?_ : Function.uncurry ⇑(clampSP T hBmeas V)
        =ᵐ[trimMeasure_T (μ := μ) T hBmeas] Function.uncurry ⇑V).trans
      (MemLp.coeFn_toLp (memLp_uncurry_trim_T T hBmeas V)).symm))
  rw [trimMeasure_T_eq_restrict]
  refine Filter.eventuallyEq_of_mem
    (self_mem_ae_restrict (MeasureTheory.measurableSet_predictable_Ioc_prod
      (𝓕 := 𝓕) 0 T MeasurableSet.univ)) (fun z hz ↦ ?_)
  obtain ⟨⟨_, hzT⟩, _⟩ := hz
  exact clampSP_apply T z.1 hBmeas V hzT z.2

include hB in
/-- **The increment-independence crux (process form).** For `t ≤ T` the finite-horizon
process `itoProcessCLM T t` of `V`'s `[0,T]` `L²` integrand reproduces `V`'s `[0,t]` discrete
Itô integral. Via the clamp: `simpleProcessL2_T T V = simpleAssembly_T T (clampSP T V)`
(`clampSP_simpleProcessL2_T`), `itoProcessCLM_simpleAssembly_T` then gives `(V'●B)_t` of the
`T`-bounded clamp, which equals `(V●B)_t` (`clampSP_itoSimpleProcess`). -/
lemma itoProcessCLM_simpleProcessL2_T (T t : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : SimpleProcess ℝ 𝓕) (ht : t ≤ T) :
    (itoProcessCLM hB T t hBmeas (simpleProcessL2_T (μ := μ) T hBmeas V) : Ω → ℝ)
      =ᵐ[μ] itoSimpleProcess hBmeas V t := by
  have hclampT : clampSP T hBmeas V ∈ TBoundedSP T hBmeas := fun p hp ↦ by
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hp)
    exact inf_le_right
  have hP1 : simpleProcessL2_T (μ := μ) T hBmeas V
      = simpleAssembly_T (μ := μ) T hBmeas ⟨clampSP T hBmeas V, hclampT⟩ :=
    (clampSP_simpleProcessL2_T T hBmeas V).symm
  rw [hP1, itoProcessCLM_simpleAssembly_T]
  exact clampSP_itoSimpleProcess T t hBmeas V ht ▸
    (memLp_itoSimpleProcess hB hBmeas (clampSP T hBmeas V) t).coeFn_toLp


end LinearStochastic.CommonHorizonClamp
