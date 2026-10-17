module

public import LinearStochastic.DeterministicVariation
public import LinearStochastic.KnownTargetControl
public import LinearStochastic.CommonStateS2

@[expose] public section

/-! An explicit continuous state for the delayed known-target control. Its
response is zero before the target is revealed, and its actual original drift
integral equation is proved for every sample and every time in the horizon. -/
noncomputable section
namespace LinearStochastic.DelayedDeterministicState
open MeasureTheory Set
open scoped NNReal Topology
open DeterministicVariation
variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  (A : E →L[ℝ] E) (B : U →L[ℝ] E) (K : ℝ → E →L[ℝ] U)

/-- The response operator is an actual exponential and Bochner integral. -/
def responseOperator (t : ℝ) : E →L[ℝ] E :=
  (NormedSpace.exp (t • A)).comp
    (∫ s in 0..t, (NormedSpace.exp ((-s) • A)).comp (B.comp (K s)))

theorem primitive_continuous (hK : Continuous K) :
    Continuous (fun s : ℝ => (NormedSpace.exp ((-s) • A)).comp (B.comp (K s))) :=
  (((differentiable_exp_smul_const ℝ A).continuous.comp continuous_neg).clm_comp
    (continuous_const.clm_comp hK))

theorem responseOperator_continuous (hK : Continuous K) : Continuous (responseOperator A B K) :=
  (differentiable_exp_smul_const ℝ A).continuous.clm_comp
    (intervalIntegral.continuous_primitive (primitive_continuous A B K hK).intervalIntegrable 0)

theorem responseOperator_apply (hK : Continuous K) (t : ℝ) (v : E) :
    responseOperator A B K t v = state A 0 (fun s => B (K s v)) t := by
  change (NormedSpace.exp (t • A)) ((∫ s in 0..t,
    (NormedSpace.exp ((-s) • A)).comp (B.comp (K s))) v) = _
  have he := (ContinuousLinearMap.apply ℝ E v).intervalIntegral_comp_comm (μ:=volume)
    ((primitive_continuous A B K hK).intervalIntegrable 0 t)
  simp only [ContinuousLinearMap.apply_apply] at he
  rw [←he]
  simp only [state,zero_add,ContinuousLinearMap.comp_apply]

omit [CompleteSpace E] in
@[simp] theorem responseOperator_zero : responseOperator A B K 0 = 0 := by
  simp only [responseOperator,intervalIntegral.integral_same,ContinuousLinearMap.comp_zero]

/-- The response is held at zero until time a. The maximum preserves actual
path continuity at the switching time. -/
def response (a : ℝ≥0) (t : ℝ≥0) : E →L[ℝ] E :=
  responseOperator A B K (max ((t : ℝ)-a) 0)

theorem response_continuous (hK : Continuous K) (a : ℝ≥0) : Continuous (response A B K a) :=
  (responseOperator_continuous A B K hK).comp
    ((NNReal.continuous_coe.sub continuous_const).max continuous_const)

omit [CompleteSpace E] in
theorem response_prefix (a t : ℝ≥0) (ht : t ≤ a) : response A B K a t = 0 := by
  simp only [response,max_eq_right (sub_nonpos.mpr (NNReal.coe_le_coe.mpr ht)),responseOperator_zero]

/-- The real integral equation for the explicit delayed response. -/
theorem response_integral (hK : Continuous K) (a T t : ℝ≥0) (ht : t ≤ T) (v : E) :
    response A B K a t v = ∫ s in Ioc 0 (t:ℝ),
      A (response A B K a s.toNNReal v) +
        B (KnownTargetControl.control a T K (fun _ : Unit => v) s.toNNReal ()) := by
  let f : ℝ → E := fun s => B (K s v)
  have hf : Continuous f := B.continuous.comp (hK.clm_apply continuous_const)
  let g : ℝ → E := fun s => A (state A 0 f (s-a))+f (s-a)
  have he : (fun s : ℝ => A (response A B K a s.toNNReal v)+
      B (KnownTargetControl.control a T K (fun _ : Unit => v) s.toNNReal ()))
      =ᵐ[volume.restrict (Ioc 0 (t:ℝ))] (Ioi (a:ℝ)).indicator g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hs0 := hs.1.le
    have hcoe := Real.coe_toNNReal s hs0
    have hsT : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr
      (hs.2.trans (NNReal.coe_le_coe.mpr ht))
    by_cases hsa : (a:ℝ)<s
    · have hmem : s.toNNReal ∈ Ioc a T := ⟨by exact_mod_cast (hcoe ▸ hsa),hsT⟩
      simp only [Set.indicator,mem_Ioi,if_pos hsa,response,hcoe,max_eq_left (sub_nonneg.mpr hsa.le),
        KnownTargetControl.control,if_pos hmem,responseOperator_apply A B K hK]
      rfl
    · have hsa' : s.toNNReal ≤ a := Real.toNNReal_le_iff_le_coe.mpr (le_of_not_gt hsa)
      simp only [Set.indicator,mem_Ioi,if_neg hsa,response_prefix A B K a _ hsa',
        zero_apply,map_zero,KnownTargetControl.zero_prefix a T K _ _ hsa',add_zero]
  rw [integral_congr_ae he,integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi]
  by_cases hat : a ≤ t
  · have hset : Ioi (a:ℝ) ∩ Ioc 0 (t:ℝ) = Ioc (a:ℝ) t := by
      ext s
      simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
      constructor
      · rintro ⟨ha,_,ht⟩; exact ⟨ha,ht⟩
      · rintro ⟨ha,ht⟩; exact ⟨ha,lt_of_le_of_lt a.coe_nonneg ha,ht⟩
    rw [hset,←intervalIntegral.integral_of_le (NNReal.coe_le_coe.mpr hat)]
    change response A B K a t v = ∫ s in (a:ℝ)..(t:ℝ),
      (fun r => A (state A 0 f r)+f r) (s-a)
    rw [intervalIntegral.integral_comp_sub_right (fun r => A (state A 0 f r)+f r) (a:ℝ),sub_self,
      ←zero_add (∫ s in 0..(t:ℝ)-a, A (state A 0 f s)+f s),
      ←integral_equation A 0 f hf]
    simp only [response,max_eq_left (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hat)),
      responseOperator_apply A B K hK]
    rfl
  · have hset : Ioi (a:ℝ) ∩ Ioc 0 (t:ℝ) = ∅ := by
      ext s
      simp only [mem_inter_iff,mem_Ioi,mem_Ioc,mem_empty_iff_false,iff_false,not_and]
      intro ha _ hs
      exact (not_le.mpr ha) (hs.trans (NNReal.coe_le_coe.mpr (le_of_not_ge hat)))
    rw [hset,Measure.restrict_empty,integral_zero_measure,response_prefix A B K a t (le_of_not_ge hat)]
    rfl

end LinearStochastic.DelayedDeterministicState
