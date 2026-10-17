module

public import LinearStochastic.CommonProcessSpace
public import LinearStochastic.DeterministicGramianControl
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

@[expose] public section

/-! A continuous deterministic steering kernel applied after time a to an
F_a-measurable L² vector is an ordinary progressive finite-energy control.
The control is explicitly zero before a and outside its prescribed interval. -/
noncomputable section
namespace LinearStochastic.KnownTargetControl
open MeasureTheory Set
open scoped NNReal
open CommonItoL2 CommonItoCLM
variable {Ω E U : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup U] [NormedSpace ℝ U]
  {𝓕 : Filtration ℝ≥0 mΩ}
  (a T : ℝ≥0) (K : ℝ → E →L[ℝ] U) (ξ : Ω → E)

/-- The actual last-interval control, with the earlier target held fixed. -/
def control (t : ℝ≥0) (ω : Ω) : U :=
  if t ∈ Ioc a T then K ((t : ℝ)-a) (ξ ω) else 0

omit [IsProbabilityMeasure μ] in
theorem measurable_template {J : Type*} [MeasurableSpace J] (s : J → ℝ≥0) (hs : Measurable s)
    (hK : Continuous K) (hξ : StronglyMeasurable ξ) :
    StronglyMeasurable (fun p : J × Ω => control a T K ξ (s p.1) p.2) := by
  have hk : StronglyMeasurable (fun p : J × Ω => K (((s p.1 : ℝ≥0) : ℝ)-a)) :=
    hK.stronglyMeasurable.comp_measurable ((NNReal.continuous_coe.measurable.comp (hs.comp measurable_fst)).sub_const _)
  have hx : StronglyMeasurable (fun p : J × Ω => ξ p.2) := hξ.comp_measurable measurable_snd
  have hv : StronglyMeasurable (fun p : J × Ω => K ((s p.1 : ℝ)-a) (ξ p.2)) :=
    (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hk.prodMk hx)
  have hi := hv.indicator ((show MeasurableSet (Ioc a T) from measurableSet_Ioc).preimage (hs.comp measurable_fst))
  convert hi using 1
  funext p
  by_cases hp : s p.1 ∈ Ioc a T
  · simp [control, hp]
  · simp [control, hp]

omit [IsProbabilityMeasure μ] in
/-- The target is only required to be known at the beginning of the final
interval. The zero prefix makes the entire control progressive. -/
theorem progressive (hK : Continuous K) (hξ : StronglyMeasurable[𝓕 a] ξ) :
    IsStronglyProgressive 𝓕 (control a T K ξ) := by
  intro t
  by_cases hat : a ≤ t
  · exact measurable_template (mΩ:=𝓕 t) a T K ξ (fun s : Iic t => s.val) measurable_subtype_coe hK
      (hξ.mono (𝓕.mono hat))
  · have he : (fun p : Iic t × Ω => control a T K ξ p.1 p.2) = fun _ => 0 := by
      funext p
      have ha : (p.1 : ℝ≥0) ≤ a := p.1.property.trans (le_of_not_ge hat)
      simp only [control,mem_Ioc,not_lt.mpr ha,false_and,if_false]
    rw [he]
    exact stronglyMeasurable_const

omit [IsProbabilityMeasure μ] mΩ in
/-- A concrete bound for the control on its full time domain. -/
theorem exists_norm_bound (hK : Continuous K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ω, ‖control a T K ξ t ω‖ ≤ M * ‖ξ ω‖ := by
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn hK.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg (K 0)).trans (hM 0 ⟨le_rfl,T.coe_nonneg⟩)
  refine ⟨M,hM0,?_⟩
  intro t ω
  by_cases ht : t ∈ Ioc a T
  · simp only [control,if_pos ht]
    apply (K ((t : ℝ)-a)).le_opNorm _ |>.trans
    apply mul_le_mul_of_nonneg_right (hM _ _) (norm_nonneg _)
    constructor
    · exact sub_nonneg.mpr (NNReal.coe_le_coe.mpr ht.1.le)
    · exact (sub_le_self _ a.coe_nonneg).trans (NNReal.coe_le_coe.mpr ht.2)
  · simp only [control,if_neg ht,norm_zero]
    exact mul_nonneg hM0 (norm_nonneg _)

/-- The explicit raw control has finite expected energy for each fixed final
interval, for arbitrary square-integrable target vectors. -/
theorem memLp (hK : Continuous K) (hξ : StronglyMeasurable[𝓕 a] ξ) (hξ2 : MemLp ξ 2 μ) :
    MemLp (Function.uncurry (control a T K ξ)) 2 ((timeMeasure_T T).prod μ) := by
  obtain ⟨M,_,hM⟩ := exists_norm_bound a T K ξ hK
  have hm : StronglyMeasurable (Function.uncurry (control a T K ξ)) :=
    measurable_template a T K ξ id measurable_id hK (hξ.mono (𝓕.le a))
  exact ((hξ2.norm.comp_snd (timeMeasure_T T)).const_mul M).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => hM z.1 z.2))

omit mΩ in
/-- The control vanishes on the entire prefix, including its switching time. -/
theorem zero_prefix (t : ℝ≥0) (ht : t ≤ a) (ω : Ω) : control a T K ξ t ω = 0 := by
  simp only [control,mem_Ioc,not_lt.mpr ht,false_and,if_false]

end LinearStochastic.KnownTargetControl
