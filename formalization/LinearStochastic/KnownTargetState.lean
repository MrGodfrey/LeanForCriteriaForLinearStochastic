module

public import LinearStochastic.DelayedDeterministicState

@[expose] public section

/-! The explicit raw state accompanying the delayed finite-energy control:
ordinary progressiveness, true continuous paths, S² and original ODE identity. -/
noncomputable section
namespace LinearStochastic.KnownTargetState
open MeasureTheory Set
open scoped NNReal Topology
open DeterministicVariation DelayedDeterministicState
variable {Ω E U : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  {𝓕 : Filtration ℝ≥0 mΩ}
  (A : E →L[ℝ] E) (B : U →L[ℝ] E) (K : ℝ → E →L[ℝ] U)
  (a T : ℝ≥0) (x : E) (ξ : Ω → E)

/-- The raw state is a deterministic free trajectory plus the delayed
exponential response to the earlier-known random displacement. -/
def path (t : ℝ≥0) (ω : Ω) : E :=
  (NormedSpace.exp ((t:ℝ) • A)) x + response A B K a t (ξ ω)

omit [IsProbabilityMeasure μ] mΩ in
/-- Every sample path is genuinely continuous, including the switching time. -/
theorem continuous (hK : Continuous K) (ω : Ω) : Continuous (fun t => path A B K a x ξ t ω) :=
  (((differentiable_exp_smul_const ℝ A).continuous.comp NNReal.continuous_coe).clm_apply continuous_const).add
    ((response_continuous A B K hK a).clm_apply continuous_const)

omit [IsProbabilityMeasure μ] in
/-- The explicit path is progressive, because its random response vanishes
until the target is known. -/
theorem progressive (hK : Continuous K) (hξ : StronglyMeasurable[𝓕 a] ξ) :
    IsStronglyProgressive 𝓕 (path A B K a x ξ) := by
  intro t
  have hfree : StronglyMeasurable[(inferInstance : MeasurableSpace (Iic t)).prod (𝓕 t)]
      (fun p : Iic t × Ω => (NormedSpace.exp ((p.1.val:ℝ) • A)) x) :=
    ((((differentiable_exp_smul_const ℝ A).continuous.comp NNReal.continuous_coe).clm_apply
      continuous_const).stronglyMeasurable.comp_measurable
        (measurable_subtype_coe.comp measurable_fst))
  by_cases hat : a ≤ t
  · apply hfree.add
    exact (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable
      (((response_continuous A B K hK a).stronglyMeasurable.comp_measurable
        (measurable_subtype_coe.comp measurable_fst)).prodMk
        ((hξ.mono (𝓕.mono hat)).comp_measurable measurable_snd))
  · have he : (fun p : Iic t × Ω => path A B K a x ξ p.1.val p.2) =
        fun p => (NormedSpace.exp ((p.1.val:ℝ) • A)) x := by
      funext p
      simp only [path,response_prefix A B K a p.1.val (p.1.property.trans (le_of_not_ge hat)),
        zero_apply,add_zero]
    rw [he]
    exact hfree

/-- A compact-interval bound yields actual finite expected supremum-square. -/
theorem squareSup (hK : Continuous K) (hξ : StronglyMeasurable[𝓕 a] ξ) (hξ2 : MemLp ξ 2 μ) :
    MemLp (ContinuousDoobL2.pathSup (path A B K a x ξ) T) 2 μ := by
  have hcompact : IsCompact (Iic T) := by rw [←Icc_bot]; exact isCompact_Icc
  obtain ⟨M0,hM0⟩ := hcompact.exists_bound_of_continuousOn
    (((differentiable_exp_smul_const ℝ A).continuous.comp NNReal.continuous_coe).clm_apply
      (continuous_const : Continuous (fun _ : ℝ≥0 => x))).continuousOn
  obtain ⟨M,hM⟩ := hcompact.exists_bound_of_continuousOn (response_continuous A B K hK a).continuousOn
  have hb (ω : Ω) : ContinuousDoobL2.pathSup (path A B K a x ξ) T ω ≤ M0+M*‖ξ ω‖ := by
    apply ciSup_le
    intro t
    exact (norm_add_le _ _).trans (add_le_add (hM0 t.val t.property)
      (((response A B K a t.val).le_opNorm (ξ ω)).trans
        (mul_le_mul_of_nonneg_right (hM t.val t.property) (norm_nonneg _))))
  have hm := CommonStateS2.pathSup_measurableOn (μ:=μ) T
    (progressive A B K a x ξ hK hξ).stronglyAdapted
    (Filter.Eventually.of_forall (fun ω => (continuous A B K a x ξ hK ω).continuousOn))
  apply ((memLp_const M0).add (hξ2.norm.const_mul M)).mono' hm
  filter_upwards [] with ω
  have hn : 0 ≤ ContinuousDoobL2.pathSup (path A B K a x ξ) T ω :=
    Real.iSup_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  exact hb ω

omit [IsProbabilityMeasure μ] mΩ [CompleteSpace E] in
theorem control_integrable (hK : Continuous K) (v : E) (t : ℝ≥0) :
    IntegrableOn (fun s : ℝ => B (KnownTargetControl.control a T K (fun _ : Unit => v) s.toNNReal ()))
      (Ioc 0 (t:ℝ)) := by
  have hc : Continuous (fun s : ℝ => B (K (((s.toNNReal:ℝ≥0):ℝ)-a) v)) :=
    B.continuous.comp ((hK.comp ((NNReal.continuous_coe.comp continuous_real_toNNReal).sub continuous_const)).clm_apply continuous_const)
  have hi : IntegrableOn (fun s : ℝ => B (K (((s.toNNReal:ℝ≥0):ℝ)-a) v)) (Ioc 0 (t:ℝ)) :=
    hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hm : MeasurableSet {s : ℝ | s.toNNReal ∈ Ioc a T} :=
    measurableSet_Ioc.preimage continuous_real_toNNReal.measurable
  have he : (fun s : ℝ => B (KnownTargetControl.control a T K (fun _ : Unit => v) s.toNNReal ())) =
      {s : ℝ | s.toNNReal ∈ Ioc a T}.indicator (fun s => B (K (((s.toNNReal:ℝ≥0):ℝ)-a) v)) := by
    funext s
    by_cases hs : s.toNNReal ∈ Ioc a T
    · simp only [KnownTargetControl.control,Set.indicator,mem_ofPred_eq,if_pos hs]
    · simp only [KnownTargetControl.control,Set.indicator,mem_ofPred_eq,if_neg hs,map_zero]
  rw [he]
  exact hi.indicator hm

omit [IsProbabilityMeasure μ] mΩ in
/-- For each time in the full horizon, the path satisfies the literal raw
zero-diffusion equation with the actual ordinary control. -/
theorem equation (hK : Continuous K) (t : ℝ≥0) (ht : t ≤ T) (ω : Ω) :
    path A B K a x ξ t ω = x + ∫ s in Ioc 0 (t:ℝ),
      A (path A B K a x ξ s.toNNReal ω)+
        B (KnownTargetControl.control a T K ξ s.toNNReal ω) := by
  have hfree : (NormedSpace.exp ((t:ℝ) • A)) x = x +
      ∫ s in Ioc 0 (t:ℝ), A ((NormedSpace.exp (s • A)) x) := by
    have he := integral_equation A x (fun _ => 0) continuous_const (t:ℝ)
    simpa only [state,map_zero,intervalIntegral.integral_zero,integral_zero,add_zero,
      intervalIntegral.integral_of_le t.coe_nonneg] using he
  have hresp := response_integral A B K hK a T t ht (ξ ω)
  change response A B K a t (ξ ω) = ∫ s in Ioc 0 (t:ℝ), A (response A B K a s.toNNReal (ξ ω))+
    B (KnownTargetControl.control a T K ξ s.toNNReal ω) at hresp
  have hI1 : IntegrableOn (fun s : ℝ => A ((NormedSpace.exp (s • A)) x)) (Ioc 0 (t:ℝ)) :=
    ((A.continuous.comp ((differentiable_exp_smul_const ℝ A).continuous.clm_apply continuous_const)).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hI2 : IntegrableOn (fun s : ℝ => A (response A B K a s.toNNReal (ξ ω))+
      B (KnownTargetControl.control a T K ξ s.toNNReal ω)) (Ioc 0 (t:ℝ)) :=
    (((A.continuous.comp (((response_continuous A B K hK a).comp continuous_real_toNNReal).clm_apply
      continuous_const)).integrableOn_Icc).mono_set Ioc_subset_Icc_self).add
        (control_integrable B K a T hK (ξ ω) t)
  rw [path,hfree,hresp,add_assoc,←integral_add hI1 hI2]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  simp only [path,map_add,Real.coe_toNNReal s hs.1.le]
  abel

end LinearStochastic.KnownTargetState
