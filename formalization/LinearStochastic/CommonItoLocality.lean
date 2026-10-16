/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
Adapted to a specified common filtration; original pinned MathFin source retained in NOTICE.
-/
import LinearStochastic.CommonStepProcess
import MathFin.Foundations.ItoIntegralLocality

noncomputable section
namespace LinearStochastic.CommonItoLocality
open MeasureTheory ProbabilityTheory Filter CommonItoCLM CommonItoL2
open scoped NNReal ENNReal Topology
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  (hB : IsPreBrownianReal B μ)

open MathFin (mulBddCLM coeFn_mulBddCLM)
/-! ### The `𝓕_a`-measurable factor, switched on after `a` -/

/-- A `𝓕_a`-measurable factor `Z`, switched on strictly after time `a`:
`(t, ω) ↦ 𝟙_{a < t}·Z ω`. The switch is not cosmetic — `(t, ω) ↦ Z ω` need not be predictable; switching it on after `a` gives
a predictable process. -/
noncomputable def afterFactor (a : ℝ≥0) (Z : Ω → ℝ) : ℝ≥0 × Ω → ℝ :=
  fun p ↦ if a < p.1 then Z p.2 else 0

omit mΩ in
/-- `afterFactor` inherits a bound on `Z` (the `max … 0` covers the switched-off
region without assuming `Ω` nonempty). -/
lemma abs_afterFactor_le {a : ℝ≥0} {Z : Ω → ℝ} {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C)
    (p : ℝ≥0 × Ω) : |afterFactor a Z p| ≤ max C 0 := by
  simp only [afterFactor]
  split_ifs with h
  · exact (hZb p.2).trans (le_max_left _ _)
  · simp

/-- **`afterFactor` is predictable.** The two-case preimage computation: on
`{a < t}` the level set is the predictable rectangle `Ioi a ×ˢ Z⁻¹(S)`
(`Z⁻¹(S) ∈ 𝓕_a`, which is exactly what generates the predictable σ-algebra),
and off it the function is constantly `0`. -/
lemma measurable_afterFactor {a : ℝ≥0} (_hBmeas : ∀ t, Measurable (B t)) {Z : Ω → ℝ}
    (hZm : Measurable[𝓕 a] Z) :
    Measurable[𝓕.predictable] (afterFactor a Z) := by
  intro S hS
  have hIoi : MeasurableSet[𝓕.predictable] (Set.Ioi a ×ˢ (Z ⁻¹' S)) :=
    MeasureTheory.measurableSet_predictable_Ioi_prod (𝓕 := 𝓕) (hZm hS)
  have hoff : MeasurableSet[𝓕.predictable] ((Set.Ioi a ×ˢ (Set.univ : Set Ω))ᶜ) :=
    (MeasureTheory.measurableSet_predictable_Ioi_prod (𝓕 := 𝓕) (i := a)
      MeasurableSet.univ).compl
  by_cases h0 : (0 : ℝ) ∈ S
  · have hset : afterFactor a Z ⁻¹' S
        = Set.Ioi a ×ˢ (Z ⁻¹' S) ∪ (Set.Ioi a ×ˢ (Set.univ : Set Ω))ᶜ := by
      ext p
      simp only [afterFactor, Set.mem_preimage, Set.mem_union, Set.mem_prod, Set.mem_Ioi,
        Set.mem_compl_iff, Set.mem_univ, and_true]
      by_cases h : a < p.1 <;> simp [h, h0]
    rw [hset]
    exact hIoi.union hoff
  · have hset : afterFactor a Z ⁻¹' S = Set.Ioi a ×ˢ (Z ⁻¹' S) := by
      ext p
      simp only [afterFactor, Set.mem_preimage, Set.mem_prod, Set.mem_Ioi]
      by_cases h : a < p.1 <;> simp [h, h0]
    rw [hset]
    exact hIoi

/-! ### Scaling a predictable `L²` integrand by a bounded `𝓕_a`-measurable factor -/

/-- **The scaling operator** `φ ↦ 𝟙_{a < t}·Z·φ` on the predictable `L²` space,
as a CLM. Total (defined on every `φ`, not just those supported after `a`) and
continuous — both properties are what the density argument consumes. -/
noncomputable def smulAdaptedCLM (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[𝓕 a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) :
    Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas) →L[ℝ]
      Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas) :=
  mulBddCLM (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas) (measurable_afterFactor hBmeas hZm)
    (abs_afterFactor_le hZb)

omit [IsProbabilityMeasure μ] in
/-- The characterising a.e. identity for `smulAdaptedCLM`. -/
theorem coeFn_smulAdaptedCLM (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[𝓕 a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    ⇑(smulAdaptedCLM T a hBmeas Z hZm C hZb φ)
      =ᵐ[trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas] fun p ↦ afterFactor a Z p * φ p :=
  coeFn_mulBddCLM _ _ _ φ

/-- Scaling a predictable `L²` integrand by a bounded `𝓕_a`-measurable factor —
which, to stay inside the predictable `L²`, must be `Z` *switched on after `a`*:
the integrand is `afterFactor a Z · φ = 𝟙_{a < t}·Z ω·φ (t,ω)`, not `Z ω·φ (t,ω)`
(the latter need not be predictable or have a predictable a.e. representative). The
switch is invisible on the integrands this file is about — those supported on
`(a, T]` — where the coefficient is exactly `Z ω·φ (t,ω)`: see
`coeFn_smulAdapted`. Unconditionally, `coeFn_smulAdapted_afterFactor`. -/
noncomputable def smulAdapted (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[𝓕 a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas) :=
  smulAdaptedCLM T a hBmeas Z hZm C hZb φ

omit [IsProbabilityMeasure μ] in
/-- `smulAdapted` unfolded: the integrand is `Z` switched on after `a`, times `φ`. -/
theorem coeFn_smulAdapted_afterFactor (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[𝓕 a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    ⇑(smulAdapted T a hBmeas Z hZm C hZb φ)
      =ᵐ[trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas] fun p ↦ afterFactor a Z p * φ p :=
  coeFn_smulAdaptedCLM T a hBmeas Z hZm C hZb φ

omit [IsProbabilityMeasure μ] in
/-- **The characterising a.e. identity for `smulAdapted`** (the API the density
argument rewrites along; without it `smulAdapted` is opaque). The support
hypothesis `hφ` is exactly what makes the switch invisible: on `[0,a]` the
integrand already vanishes, so `𝟙_{a<t}·Z·φ = Z·φ`. -/
theorem coeFn_smulAdapted (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[𝓕 a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas), p.1 ≤ a → φ p = 0) :
    ⇑(smulAdapted T a hBmeas Z hZm C hZb φ)
      =ᵐ[trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas] fun p ↦ Z p.2 * φ p := by
  filter_upwards [coeFn_smulAdapted_afterFactor T a hBmeas Z hZm C hZb φ, hφ] with p e1 e2
  rw [e1]
  simp only [afterFactor]
  split_ifs with h
  · rfl
  · rw [e2 (not_lt.mp h), mul_zero, mul_zero]

/-- **Restriction to `(a, T]`** — the `Z = 1` instance of `smulAdaptedCLM`. On `L²`
this is the orthogonal projection onto the integrands supported after `a`. -/
noncomputable def restrictAfterCLM (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas) →L[ℝ]
      Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas) :=
  smulAdaptedCLM T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1 (fun _ ↦ abs_one.le)

omit [IsProbabilityMeasure μ] in
/-- **On an integrand already supported after `a` the restriction is the identity.** -/
theorem restrictAfterCLM_eq (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas), p.1 ≤ a → φ p = 0) :
    restrictAfterCLM T a hBmeas φ = φ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_smulAdaptedCLM T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
    (fun _ ↦ abs_one.le) φ, hφ] with p e1 e2
  rw [show (restrictAfterCLM T a hBmeas φ : ℝ≥0 × Ω → ℝ) p
      = afterFactor a (fun _ ↦ (1 : ℝ)) p * (φ : ℝ≥0 × Ω → ℝ) p from e1]
  simp only [afterFactor]
  split_ifs with h
  · rw [one_mul]
  · rw [zero_mul, e2 (not_lt.mp h)]

omit [IsProbabilityMeasure μ] in
/-- **`restrictAfterCLM` unfolded** — the unconditional companion of
`restrictAfterCLM_eq`: the integrand switched on strictly after `a`. -/
theorem coeFn_restrictAfterCLM (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    ⇑(restrictAfterCLM T a hBmeas φ) =ᵐ[trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas]
      fun p ↦ if a < p.1 then φ p else 0 := by
  filter_upwards [coeFn_smulAdaptedCLM T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
    (fun _ ↦ abs_one.le) φ] with p hp
  rw [show ⇑(restrictAfterCLM T a hBmeas φ) p
      = afterFactor a (fun _ ↦ (1 : ℝ)) p * (φ : ℝ≥0 × Ω → ℝ) p from hp]
  simp only [afterFactor]
  split_ifs <;> simp

/-! ### Simple processes restarted at `a` -/

/-- The time origin `{0}` is `trim_T`-null, so pointwise identities off it are a.e.
identities. (`trim_T` is the *predictable* trim: the fibre is a bottom rectangle.) -/
lemma ae_fst_ne_zero (T : ℝ≥0) (hBmeas : ∀ t, Measurable (B t)) :
    ∀ᵐ p ∂(trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas), p.1 ≠ 0 := by
  have hbot : MeasurableSet[𝓕.predictable] (({(⊥ : ℝ≥0)} : Set ℝ≥0) ×ˢ (Set.univ : Set Ω)) :=
    MeasureTheory.measurableSet_predictable_singleton_bot_prod (𝓕 := 𝓕) MeasurableSet.univ
  have htime : timeMeasure_T T ({(⊥ : ℝ≥0)} : Set ℝ≥0) = 0 :=
    nonpos_iff_eq_zero.mp
      ((Measure.restrict_apply_le _ _).trans
        (CommonItoL2.timeMeasure_singleton (⊥ : ℝ≥0)).le)
  have hnull : (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)
      (({(⊥ : ℝ≥0)} : Set ℝ≥0) ×ˢ (Set.univ : Set Ω)) = 0 := by
    unfold trimMeasure_T
    rw [MeasureTheory.trim_measurableSet_eq _ hbot, Measure.prod_prod, htime, zero_mul]
  have hset : {p : ℝ≥0 × Ω | ¬ p.1 ≠ 0}
      = ({(⊥ : ℝ≥0)} : Set ℝ≥0) ×ˢ (Set.univ : Set Ω) := by
    ext p
    simp
  rw [ae_iff, hset]
  exact hnull

/-- A finite sum of simple processes evaluates pointwise as the sum of the values. -/
lemma coe_simpleProcess_sum {ι' : Type*}
    (s : Finset ι') (W : ι' → SimpleProcess ℝ 𝓕)
    (t : ℝ≥0) (ω : Ω) : ⇑(∑ i ∈ s, W i) t ω = ∑ i ∈ s, ⇑(W i) t ω := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, SimpleProcess.coe_add]
      simp [ih]

/-- A single step evaluates to the indicator of its rectangle. -/
lemma coe_stepSP {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {a' b : ℝ≥0}
    (hab : a' ≤ b) (hbT : b ≤ T) {ψ : Ω → ℝ}
    (hψm : Measurable[𝓕 a'] ψ) {M : ℝ} (hψM : ∀ ω, |ψ ω| ≤ M)
    (t : ℝ≥0) (ω : Ω) :
    ⇑(stepSP hBmeas hab hbT hψm hψM : TBoundedSP (𝓕 := 𝓕) T hBmeas).val t ω
      = (Set.Ioc a' b).indicator (fun _ ↦ ψ ω) t := by
  rw [SimpleProcess.apply_eq]
  have hbot : ({(⊥ : ℝ≥0)} : Set ℝ≥0).indicator
      (fun _ ↦ (stepSP hBmeas hab hbT hψm hψM :
        TBoundedSP (𝓕 := 𝓕) T hBmeas).val.valueBot ω) t = 0 := by
    simp [stepSP]
  rw [hbot, zero_add]
  show (Finsupp.single (a', b) ψ).sum
      (fun p v ↦ (Set.Ioc p.1 p.2).indicator (fun _ ↦ v ω) t) = _
  rw [Finsupp.sum_single_index (by simp)]

/-- **`V` restarted at `a`, scaled by `Z`.** Each rectangle `(p.1, p.2]` of `V` is
cut down to `(a ⊔ p.1, p.2]` (empty, and dropped, when that is degenerate) and its
coefficient is multiplied by `Z`. The result is again a `T`-bounded simple process:
the new coefficient `Z·V(p)` is `𝓕_{a ⊔ p.1}`-measurable because `Z` is
`𝓕_a`-measurable and `V(p)` is `𝓕_{p.1}`-measurable — this is the one place where
`a ≤ a ⊔ p.1` earns the support hypothesis its keep. -/
noncomputable def afterStepSP (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[𝓕 a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP (𝓕 := 𝓕) T hBmeas) : TBoundedSP (𝓕 := 𝓕) T hBmeas :=
  ∑ p ∈ V.val.value.support.attach,
    if h : a ⊔ p.val.1 ≤ p.val.2 then
      stepSP hBmeas h (V.property p.val p.property)
        (φ := fun ω ↦ Z ω * V.val.value p.val ω)
        ((hZm.mono (𝓕.mono le_sup_left) le_rfl).mul
          ((V.val.measurable_value p.val).mono
            (𝓕.mono le_sup_right) le_rfl))
        (M := C * V.val.valueBound)
        (fun ω ↦ by
          rw [abs_mul]
          exact mul_le_mul (hZb ω)
            (by rw [← Real.norm_eq_abs]; exact V.val.value_le_valueBound p.val ω)
            (abs_nonneg _) ((abs_nonneg (Z ω)).trans (hZb ω)))
    else 0

/-- **The defining pointwise identity of `afterStepSP`**: off the time origin it is
`𝟙_{a < t}·Z·V`. -/
lemma coe_afterStepSP (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[𝓕 a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP (𝓕 := 𝓕) T hBmeas) {t : ℝ≥0} (ht : t ≠ 0) (ω : Ω) :
    ⇑(afterStepSP T a hBmeas Z hZm C hZb V).val t ω
      = afterFactor a Z (t, ω) * ⇑V.val t ω := by
  have htbot : t ∉ ({(⊥ : ℝ≥0)} : Set ℝ≥0) := by
    simp only [Set.mem_singleton_iff, NNReal.bot_eq_zero]
    exact ht
  have hV : ⇑V.val t ω
      = ∑ p ∈ V.val.value.support,
          (Set.Ioc p.1 p.2).indicator (fun _ ↦ V.val.value p ω) t := by
    rw [SimpleProcess.apply_eq, Set.indicator_of_notMem htbot, zero_add, Finsupp.sum]
  rw [afterStepSP, AddSubmonoidClass.coe_finsetSum, coe_simpleProcess_sum, hV, Finset.mul_sum,
    ← Finset.sum_attach V.val.value.support
      (fun q ↦ afterFactor a Z (t, ω) * (Set.Ioc q.1 q.2).indicator
        (fun _ ↦ V.val.value q ω) t)]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hle : a ⊔ p.val.1 ≤ p.val.2
  · rw [dif_pos hle, coe_stepSP]
    simp only [afterFactor]
    by_cases hat : a < t
    · have hmem : t ∈ Set.Ioc (a ⊔ p.val.1) p.val.2 ↔ t ∈ Set.Ioc p.val.1 p.val.2 := by
        simp only [Set.mem_Ioc, sup_lt_iff]
        exact ⟨fun h ↦ ⟨h.1.2, h.2⟩, fun h ↦ ⟨⟨hat, h.1⟩, h.2⟩⟩
      by_cases hin : t ∈ Set.Ioc p.val.1 p.val.2
      · rw [Set.indicator_of_mem (hmem.mpr hin), Set.indicator_of_mem hin, if_pos hat]
      · rw [Set.indicator_of_notMem (fun hc ↦ hin (hmem.mp hc)), Set.indicator_of_notMem hin,
          mul_zero]
    · rw [if_neg hat, zero_mul]
      exact Set.indicator_of_notMem (fun hc ↦ hat (lt_of_le_of_lt le_sup_left hc.1)) _
  · rw [dif_neg hle]
    have hzero : ⇑((0 : TBoundedSP (𝓕 := 𝓕) T hBmeas).val) t ω = 0 := by simp
    rw [hzero, eq_comm]
    simp only [afterFactor]
    by_cases hat : a < t
    · rw [Set.indicator_of_notMem (fun hc ↦ hle (sup_le (hat.le.trans hc.2) (hc.1.le.trans hc.2))),
        mul_zero]
    · rw [if_neg hat, zero_mul]

variable [CommonItoIsometry.ForwardIndependent B 𝓕 μ]

/-- **The simple-process bridge.** Embedding the restarted process is the same as
scaling the embedding. -/
lemma simpleAssembly_T_afterStepSP (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[𝓕 a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP (𝓕 := 𝓕) T hBmeas) :
    simpleAssembly_T (𝓕 := 𝓕) (μ := μ) T hBmeas (afterStepSP T a hBmeas Z hZm C hZb V)
      = smulAdaptedCLM T a hBmeas Z hZm C hZb (simpleAssembly_T (𝓕 := 𝓕) (μ := μ) T hBmeas V) := by
  refine Lp.ext ?_
  filter_upwards [(memLp_uncurry_trim_T (μ := μ) T hBmeas
      (afterStepSP T a hBmeas Z hZm C hZb V).val).coeFn_toLp,
    coeFn_smulAdaptedCLM T a hBmeas Z hZm C hZb (simpleAssembly_T (𝓕 := 𝓕) (μ := μ) T hBmeas V),
    (memLp_uncurry_trim_T (μ := μ) T hBmeas V.val).coeFn_toLp,
    ae_fst_ne_zero (μ := μ) T hBmeas] with p e1 e2 e3 hp
  rw [show (simpleAssembly_T (𝓕 := 𝓕) (μ := μ) T hBmeas (afterStepSP T a hBmeas Z hZm C hZb V) :
        ℝ≥0 × Ω → ℝ) p
      = Function.uncurry ⇑(afterStepSP T a hBmeas Z hZm C hZb V).val p from e1, e2,
    show (simpleAssembly_T (𝓕 := 𝓕) (μ := μ) T hBmeas V : ℝ≥0 × Ω → ℝ) p
      = Function.uncurry ⇑V.val p from e3]
  obtain ⟨t, ω⟩ := p
  exact coe_afterStepSP T a hBmeas Z hZm C hZb V hp ω

/-- The elementary integral of the restarted process, term by term. -/
lemma itoSimple_afterStepSP_eq (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[𝓕 a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP (𝓕 := 𝓕) T hBmeas) (ω : Ω) :
    CommonItoL2.itoSimple hBmeas (afterStepSP T a hBmeas Z hZm C hZb V).val ω
      = ∑ p ∈ V.val.value.support.attach,
          if _h : a ⊔ p.val.1 ≤ p.val.2 then
            Z ω * V.val.value p.val ω * (B p.val.2 ω - B (a ⊔ p.val.1) ω) else 0 := by
  rw [afterStepSP, AddSubmonoidClass.coe_finsetSum, itoSimple_sum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hle : a ⊔ p.val.1 ≤ p.val.2
  · rw [dif_pos hle, dif_pos hle, itoSimple_stepSP]
  · rw [dif_neg hle, dif_neg hle]
    simp [CommonItoL2.itoSimple]

/-- **The scaling passes through the elementary integral**: `Z` factors out of the
finite increment sum. -/
lemma itoSimple_afterStepSP_smul (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[𝓕 a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C) (V : TBoundedSP (𝓕 := 𝓕) T hBmeas) (ω : Ω) :
    CommonItoL2.itoSimple hBmeas (afterStepSP T a hBmeas Z hZm C hZb V).val ω
      = Z ω * CommonItoL2.itoSimple hBmeas
          (afterStepSP T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
            (fun _ ↦ abs_one.le) V).val ω := by
  rw [itoSimple_afterStepSP_eq, itoSimple_afterStepSP_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  by_cases hle : a ⊔ p.val.1 ≤ p.val.2
  · rw [dif_pos hle, dif_pos hle]; ring
  · rw [dif_neg hle, dif_neg hle, mul_zero]

/-! ### `𝓕_a`-linearity -/


/-- **`𝓕_a`-linearity of the Itô integral.** A bounded `𝓕_a`-measurable factor
passes through the stochastic integral of an integrand supported on `(a, T]`. -/
theorem itoIntegralCLM_T_smulAdapted (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[𝓕 a] Z)
    (C : ℝ) (hZb : ∀ ω, |Z ω| ≤ C)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas), p.1 ≤ a → φ p = 0) :
    ⇑(itoIntegralCLM_T hB T hBmeas (smulAdapted T a hBmeas Z hZm C hZb φ))
      =ᵐ[μ] fun ω ↦ Z ω * itoIntegralCLM_T hB T hBmeas φ ω := by
  -- multiplication by `Z` on the sample side
  have hZmΩ : Measurable Z := hZm.mono (𝓕.le a) le_rfl
  -- the two continuous maps agree on the dense simple embeddings, hence everywhere
  have hEq : (itoIntegralCLM_T hB T hBmeas).comp (smulAdaptedCLM T a hBmeas Z hZm C hZb)
      = (mulBddCLM μ hZmΩ hZb).comp
          ((itoIntegralCLM_T hB T hBmeas).comp (restrictAfterCLM T a hBmeas)) := by
    refine ContinuousLinearMap.ext fun ψ ↦ ?_
    refine congrFun (DenseRange.equalizer (simpleAssembly_T_denseRange (𝓕 := 𝓕) (μ := μ) T hBmeas)
      (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
      (funext fun V ↦ ?_)) ψ
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
    -- `V` restarted at `a` unscaled: the `Z = 1` companion of `afterStepSP … Z … V`.
    set U := afterStepSP T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1 (fun _ ↦ abs_one.le) V
    rw [← simpleAssembly_T_afterStepSP T a hBmeas Z hZm C hZb V,
      show restrictAfterCLM T a hBmeas (simpleAssembly_T (𝓕 := 𝓕) (μ := μ) T hBmeas V)
          = simpleAssembly_T (𝓕 := 𝓕) (μ := μ) T hBmeas U from
        (simpleAssembly_T_afterStepSP T a hBmeas (fun _ ↦ (1 : ℝ)) measurable_const 1
          (fun _ ↦ abs_one.le) V).symm,
      itoIntegralCLM_T_simpleAssembly_T, itoIntegralCLM_T_simpleAssembly_T]
    refine Lp.ext ?_
    filter_upwards [(CommonItoL2.memLp_itoSimple hB hBmeas
        (afterStepSP T a hBmeas Z hZm C hZb V).val).coeFn_toLp,
      coeFn_mulBddCLM μ hZmΩ hZb (CommonItoL2.itoSimpleLp hB hBmeas U.val),
      (CommonItoL2.memLp_itoSimple hB hBmeas U.val).coeFn_toLp] with ω f1 f2 f3
    rw [show (CommonItoL2.itoSimpleLp hB hBmeas
          (afterStepSP T a hBmeas Z hZm C hZb V).val : Ω → ℝ) ω
        = CommonItoL2.itoSimple hBmeas (afterStepSP T a hBmeas Z hZm C hZb V).val ω from f1,
      f2, show (CommonItoL2.itoSimpleLp hB hBmeas U.val : Ω → ℝ) ω
        = CommonItoL2.itoSimple hBmeas U.val ω from f3]
    exact itoSimple_afterStepSP_smul T a hBmeas Z hZm C hZb V ω
  have h1 := DFunLike.congr_fun hEq φ
  simp only [ContinuousLinearMap.comp_apply, restrictAfterCLM_eq T a hBmeas φ hφ] at h1
  rw [show smulAdapted T a hBmeas Z hZm C hZb φ
      = smulAdaptedCLM T a hBmeas Z hZm C hZb φ from rfl, h1]
  exact coeFn_mulBddCLM μ hZmΩ hZb _

/-- **Unbounded `Z`.** The hypothesis is exactly that the *product* `Z·φ` is a
legitimate `L²` integrand; nothing is assumed about the moments of `Z` alone.
Localise on the `𝓕_a`-sets `{|Z| ≤ M}`: on each of them the bounded theorem
applies twice — with factor `𝟙_{|Z|≤M}` against the integrand `Z·φ`, and with
factor `𝟙_{|Z|≤M}·Z` against `φ` — and the two scaled integrands coincide. The
sets exhaust `Ω`, so the a.e. identities glue. -/
theorem itoIntegralCLM_T_smulAdapted_of_memLp (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[𝓕 a] Z)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas), p.1 ≤ a → φ p = 0)
    (hZφ : MemLp (fun p : ℝ≥0 × Ω ↦ Z p.2 * φ p) 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)) :
    ⇑(itoIntegralCLM_T hB T hBmeas (hZφ.toLp _))
      =ᵐ[μ] fun ω ↦ Z ω * itoIntegralCLM_T hB T hBmeas φ ω := by
  set ψ := hZφ.toLp (fun p : ℝ≥0 × Ω ↦ Z p.2 * φ p)
  have hψ : ∀ᵐ p ∂(trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas), p.1 ≤ a → ψ p = 0 := by
    filter_upwards [hZφ.coeFn_toLp, hφ] with p e1 e2 h
    rw [show (ψ : ℝ≥0 × Ω → ℝ) p = Z p.2 * (φ : ℝ≥0 × Ω → ℝ) p from e1, e2 h, mul_zero]
  have key : ∀ M : ℕ, ∀ᵐ ω ∂μ, |Z ω| ≤ (M : ℝ) →
      (itoIntegralCLM_T hB T hBmeas ψ) ω = Z ω * (itoIntegralCLM_T hB T hBmeas φ) ω := by
    intro M
    have hAm : MeasurableSet[𝓕 a] {ω | |Z ω| ≤ (M : ℝ)} := by
      rw [show {ω | |Z ω| ≤ (M : ℝ)} = Z ⁻¹' (Set.Icc (-(M : ℝ)) (M : ℝ)) from by
        ext ω; simp [abs_le]]
      exact hZm measurableSet_Icc
    have hg1m : Measurable[𝓕 a]
        (Set.indicator {ω | |Z ω| ≤ (M : ℝ)} (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hAm
    have hg1b (ω : Ω) : |Set.indicator {ω | |Z ω| ≤ (M : ℝ)} (fun _ ↦ (1 : ℝ)) ω| ≤ 1 := by
      by_cases hm : ω ∈ {ω | |Z ω| ≤ (M : ℝ)}
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
    have hgZm : Measurable[𝓕 a]
        (Set.indicator {ω | |Z ω| ≤ (M : ℝ)} Z) := hZm.indicator hAm
    have hgZb (ω : Ω) : |Set.indicator {ω | |Z ω| ≤ (M : ℝ)} Z ω| ≤ (M : ℝ) := by
      by_cases hm : ω ∈ {ω | |Z ω| ≤ (M : ℝ)}
      · rw [Set.indicator_of_mem hm]; exact hm
      · simp [Set.indicator_of_notMem hm]
    have E1 := itoIntegralCLM_T_smulAdapted hB T a hBmeas _ hg1m 1 hg1b ψ hψ
    have E2 := itoIntegralCLM_T_smulAdapted hB T a hBmeas _ hgZm (M : ℝ) hgZb φ hφ
    have hsame : smulAdapted T a hBmeas _ hg1m 1 hg1b ψ
        = smulAdapted T a hBmeas _ hgZm (M : ℝ) hgZb φ := by
      refine Lp.ext ?_
      filter_upwards [coeFn_smulAdapted_afterFactor T a hBmeas _ hg1m 1 hg1b ψ,
        coeFn_smulAdapted_afterFactor T a hBmeas _ hgZm (M : ℝ) hgZb φ,
        hZφ.coeFn_toLp] with p f1 f2 f3
      rw [f1, f2, show (ψ : ℝ≥0 × Ω → ℝ) p = Z p.2 * (φ : ℝ≥0 × Ω → ℝ) p from f3]
      simp only [afterFactor]
      split_ifs with h
      · by_cases hm : p.2 ∈ {ω | |Z ω| ≤ (M : ℝ)}
        · simp [Set.indicator_of_mem hm]
        · simp [Set.indicator_of_notMem hm]
      · rw [zero_mul, zero_mul]
    rw [hsame] at E1
    filter_upwards [E1, E2] with ω h1 h2 hω
    have hmem : ω ∈ {ω | |Z ω| ≤ (M : ℝ)} := hω
    have h3 := h1.symm.trans h2
    rwa [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, one_mul] at h3
  filter_upwards [ae_all_iff.mpr key] with ω hω
  obtain ⟨M, hM⟩ := exists_nat_ge |Z ω|
  exact hω M hM

/-- **The hypothesis in its sample-side form.** `itoIntegralCLM_T_smulAdapted_of_memLp`
asks for `Z·φ ∈ L²(trim)`; a caller whose `φ` came out of an Itô formula knows nothing
about it, but does know `∫φ dB`, and so can offer `Z·∫φ dB ∈ L²(μ)` instead. The Itô
isometry makes these the same requirement: truncating `Z` at level `M` gives genuine
integrands `𝟙_{|Z|≤M}·Z·φ` whose energies *are* the sample-side energies
`‖𝟙_{|Z|≤M}·Z·∫φ dB‖ ≤ ‖Z·∫φ dB‖`, uniformly bounded; they converge pointwise to `Z·φ`,
so Fatou bounds its energy too. The extra `⇑ψ =ᵐ Z·φ` conclusion is what lets a caller
inherit the *support* of `φ`. -/
theorem itoIntegralCLM_T_smul_of_memLp (T a : ℝ≥0) (hBmeas : ∀ t, Measurable (B t))
    (Z : Ω → ℝ) (hZm : Measurable[𝓕 a] Z)
    (φ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas))
    (hφ : ∀ᵐ p ∂(trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas), p.1 ≤ a → φ p = 0)
    (hZI : MemLp (fun ω ↦ Z ω * itoIntegralCLM_T hB T hBmeas φ ω) 2 μ) :
    ∃ ψ : Lp ℝ 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas),
      (⇑ψ =ᵐ[trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas] fun p ↦ Z p.2 * φ p) ∧
      ⇑(itoIntegralCLM_T hB T hBmeas ψ)
        =ᵐ[μ] fun ω ↦ Z ω * itoIntegralCLM_T hB T hBmeas φ ω := by
  -- the truncations `Z_M = 𝟙_{|Z| ≤ M}·Z`, bounded and `𝓕_a`-measurable
  have hAm (M : ℕ) : MeasurableSet[𝓕 a]
      {ω | |Z ω| ≤ (M : ℝ)} := by
    rw [show {ω | |Z ω| ≤ (M : ℝ)} = Z ⁻¹' (Set.Icc (-(M : ℝ)) (M : ℝ)) from by
      ext ω; simp [abs_le]]
    exact hZm measurableSet_Icc
  have hZMm (M : ℕ) : Measurable[𝓕 a]
      (Set.indicator {ω | |Z ω| ≤ (M : ℝ)} Z) := hZm.indicator (hAm M)
  have hZMb (M : ℕ) (ω : Ω) : |Set.indicator {ω | |Z ω| ≤ (M : ℝ)} Z ω| ≤ (M : ℝ) := by
    by_cases hm : ω ∈ {ω | |Z ω| ≤ (M : ℝ)}
    · rw [Set.indicator_of_mem hm]; exact hm
    · simp [Set.indicator_of_notMem hm]
  -- their energies are bounded by the sample-side one, through the Itô isometry
  have hbound (M : ℕ) :
      ‖smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ‖ ≤ ‖hZI.toLp _‖ := by
    rw [← itoIntegralCLM_T_norm hB T hBmeas (smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ)]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [itoIntegralCLM_T_smulAdapted hB T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ hφ,
      hZI.coeFn_toLp] with ω h1 h2
    rw [h1, h2, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    by_cases hm : ω ∈ {ω | |Z ω| ≤ (M : ℝ)}
    · rw [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm, abs_zero]; exact abs_nonneg _
  -- Fatou: the limit integrand `Z·φ` inherits the bound
  have hZφ : MemLp (fun p : ℝ≥0 × Ω ↦ Z p.2 * φ p) 2 (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas) := by
    have hmeas : AEStronglyMeasurable[𝓕.predictable]
        (fun p : ℝ≥0 × Ω ↦ Z p.2 * φ p) (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas) := by
      refine AEStronglyMeasurable.congr
        ((measurable_afterFactor hBmeas hZm).stronglyMeasurable.aestronglyMeasurable.mul
          (Lp.aestronglyMeasurable φ)) ?_
      filter_upwards [hφ] with p hp
      simp only [Pi.mul_apply, afterFactor]
      split_ifs with hc
      · rfl
      · rw [hp (not_lt.mp hc), mul_zero, mul_zero]
    have hlim : ∀ᵐ p ∂(trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas),
        Tendsto (fun M : ℕ ↦
            (smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ : ℝ≥0 × Ω → ℝ) p)
          atTop (𝓝 (Z p.2 * φ p)) := by
      filter_upwards [ae_all_iff.mpr (fun M : ℕ ↦
        coeFn_smulAdapted_afterFactor T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ), hφ] with p hall hp
      rcases le_or_gt p.1 a with hle | hlt
      · have hz (M : ℕ) :
            (smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ : ℝ≥0 × Ω → ℝ) p = 0 := by
          rw [hall M]
          simp only [afterFactor, if_neg (not_lt.mpr hle), zero_mul]
        simp only [hz, hp hle, mul_zero]
        exact tendsto_const_nhds
      · refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [eventually_ge_atTop ⌈|Z p.2|⌉₊] with M hM
        have hmem : p.2 ∈ {ω | |Z ω| ≤ (M : ℝ)} :=
          (Nat.le_ceil |Z p.2|).trans (Nat.cast_le.mpr hM)
        rw [hall M]
        simp only [afterFactor, if_pos hlt, Set.indicator_of_mem hmem]
    have hle : atTop.liminf (fun M : ℕ ↦ eLpNorm
        (⇑(smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ)) 2
          (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas))
        ≤ ENNReal.ofReal ‖hZI.toLp (fun ω ↦ Z ω * itoIntegralCLM_T hB T hBmeas φ ω)‖ := by
      refine liminf_le_of_frequently_le' (Filter.Frequently.of_forall fun M ↦ ?_)
      rw [show eLpNorm (⇑(smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ)) 2
            (trimMeasure_T (𝓕 := 𝓕) (μ := μ) T hBmeas)
          = ENNReal.ofReal ‖smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ‖ from by
        rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]]
      exact ENNReal.ofReal_le_ofReal (hbound M)
    exact ⟨hmeas, lt_of_le_of_lt ((MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun M : ℕ ↦ Lp.aestronglyMeasurable
        (smulAdapted T a hBmeas _ (hZMm M) (M : ℝ) (hZMb M) φ)) _ hlim).trans hle)
      ENNReal.ofReal_lt_top⟩
  exact ⟨hZφ.toLp _, hZφ.coeFn_toLp,
    itoIntegralCLM_T_smulAdapted_of_memLp hB T a hBmeas Z hZm φ hφ hZφ⟩


end LinearStochastic.CommonItoLocality
