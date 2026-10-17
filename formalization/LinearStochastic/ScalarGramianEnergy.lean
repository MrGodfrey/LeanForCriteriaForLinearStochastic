module

public import LinearStochastic.KnownTargetSolution
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! An explicit scalar member of the genuine Gramian family. Its delayed
control energy is computed exactly, allowing an actual divergence example. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.ScalarGramianEnergy
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

/-- The scalar system dy=u dt satisfies the true power observability test. -/
theorem observable : ∀ v : ℝ,
    (∀ k : ℕ, (ContinuousLinearMap.id ℝ ℝ).adjoint
      (((0 : ℝ →L[ℝ] ℝ).adjoint^k) v)=0) → v=0 := by
  intro v hv
  simpa only [pow_zero,one_apply_eq_self,ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply] using hv 0

/-- Its actual integrated exponential Gramian is h times the identity. -/
theorem gramian_scalar (h : ℝ) (hh : 0 < h) :
    DeterministicGramian.gramian (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ) h =
      h • ContinuousLinearMap.id ℝ ℝ := by
  simp [DeterministicGramian.gramian,DeterministicGramian.observation,
    NormedSpace.exp_zero,map_zero,hh.le]
  ext
  rfl

/-- The inverse is the genuine proved Gramian inverse, whose kernel is 1/h. -/
theorem kernel_scalar (h : ℝ) (hh : 0 < h) (t x : ℝ) :
    DeterministicGramianControl.kernel (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ)
      h hh observable t x=x/h := by
  have hi := DeterministicGramian.gramian_inverse (0 : ℝ →L[ℝ] ℝ)
    (ContinuousLinearMap.id ℝ ℝ) h hh observable x
  rw [gramian_scalar h hh] at hi
  change h * (DeterministicGramian.gramianEquiv (0 : ℝ →L[ℝ] ℝ)
    (ContinuousLinearMap.id ℝ ℝ) h hh observable).symm x=x at hi
  simp only [DeterministicGramianControl.kernel,DeterministicGramian.observation,
    ContinuousLinearMap.adjoint_id,map_zero,smul_zero,
    NormedSpace.exp_zero,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.id_apply,one_apply_eq_self]
  exact (eq_div_iff hh.ne').mpr (by simpa only [mul_comm] using hi)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {W : ℝ≥0 → Ω → ℝ} (hW : IsPreBrownianReal W μ) (hWm : ∀ t, Measurable (W t))

/-- The actual scalar Gramian control: zero up to a, then W_a/(T-a). -/
def control (a T : ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if t∈Ioc a T then W a ω/((T:ℝ)-a) else 0

omit mΩ in
/-- This is exactly the previously constructed Gramian steering control. -/
theorem control_is_gramian (a T : ℝ≥0) (ha : a<T) :
    control (W:=W) a T = KnownTargetControl.control a T
      (DeterministicGramianControl.kernel (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ)
        ((T:ℝ)-a) (sub_pos.mpr (NNReal.coe_lt_coe.mpr ha)) observable) (W a) := by
  funext t ω
  simp only [control,KnownTargetControl.control,kernel_scalar]

include hW hWm in
omit [IsProbabilityMeasure μ] in
/-- Exact expected energy, using the actual Brownian second moment. -/
theorem energy (a T : ℝ≥0) (ha : a<T) :
    (∫ t in Ioc 0 (T:ℝ), ∫ ω, ‖control (W:=W) a T t.toNNReal ω‖^2 ∂μ) =
      (a:ℝ)/((T:ℝ)-a) := by
  have hh : 0<(T:ℝ)-a := sub_pos.mpr (NNReal.coe_lt_coe.mpr ha)
  have he : (fun t : ℝ=>∫ ω, ‖control (W:=W) a T t.toNNReal ω‖^2 ∂μ) =ᵐ[volume.restrict (Ioc 0 (T:ℝ))]
      (Ioc (a:ℝ) T).indicator (fun _=> (a:ℝ)/((T:ℝ)-a)^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hcoe : (t.toNNReal:ℝ)=t := Real.coe_toNNReal t ht.1.le
    by_cases hat : (a:ℝ)<t
    · have hm : t.toNNReal∈Ioc a T := ⟨by exact_mod_cast (hcoe ▸ hat),Real.toNNReal_le_iff_le_coe.mpr ht.2⟩
      simp only [control,if_pos hm,Real.norm_eq_abs,sq_abs,div_pow,integral_div,
        CommonItoIsometry.integral_eval_sq hW hWm a,Set.indicator_of_mem (show t∈Ioc (a:ℝ) T from ⟨hat,ht.2⟩)]
    · have hm : t.toNNReal∉Ioc a T := fun h=>hat (by have hh := NNReal.coe_lt_coe.mpr h.1; simpa only [hcoe] using hh)
      simp only [control,if_neg hm,norm_zero,zero_pow (by decide : 2≠0),integral_zero,
        Set.indicator_of_notMem (show t∉Ioc (a:ℝ) T from fun h=>hat h.1)]
  rw [integral_congr_ae he,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  have hi : Ioc (a:ℝ) T ∩ Ioc 0 (T:ℝ)=Ioc (a:ℝ) T :=
    inter_eq_left.mpr (Ioc_subset_Ioc_left a.coe_nonneg)
  rw [hi,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,ENNReal.toReal_ofReal hh.le,smul_eq_mul]
  field_simp

omit mΩ in
/-- The energy is also computed sample by sample, in the paper's original
order E∫dt. Thus the result does not rely on an unproved interchange. -/
theorem sample_energy (a T : ℝ≥0) (ha : a<T) (ω : Ω) :
    (∫ t in Ioc 0 (T:ℝ), ‖control (W:=W) a T t.toNNReal ω‖^2) =
      (W a ω)^2/((T:ℝ)-a) := by
  have hh : 0<(T:ℝ)-a := sub_pos.mpr (NNReal.coe_lt_coe.mpr ha)
  have he : (fun t : ℝ=>‖control (W:=W) a T t.toNNReal ω‖^2) =ᵐ[volume.restrict (Ioc 0 (T:ℝ))]
      (Ioc (a:ℝ) T).indicator (fun _=> (W a ω)^2/((T:ℝ)-a)^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hcoe : (t.toNNReal:ℝ)=t := Real.coe_toNNReal t ht.1.le
    by_cases hat : (a:ℝ)<t
    · have hm : t.toNNReal∈Ioc a T := ⟨by exact_mod_cast (hcoe ▸ hat),Real.toNNReal_le_iff_le_coe.mpr ht.2⟩
      simp only [control,if_pos hm,Real.norm_eq_abs,sq_abs,div_pow,
        Set.indicator_of_mem (show t∈Ioc (a:ℝ) T from ⟨hat,ht.2⟩)]
    · have hm : t.toNNReal∉Ioc a T := fun h=>hat (by
        have hh := NNReal.coe_lt_coe.mpr h.1; simpa only [hcoe] using hh)
      simp only [control,if_neg hm,norm_zero,zero_pow (by decide : 2≠0),
        Set.indicator_of_notMem (show t∉Ioc (a:ℝ) T from fun h=>hat h.1)]
  rw [integral_congr_ae he,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  have hi : Ioc (a:ℝ) T ∩ Ioc 0 (T:ℝ)=Ioc (a:ℝ) T :=
    inter_eq_left.mpr (Ioc_subset_Ioc_left a.coe_nonneg)
  rw [hi,integral_const]
  simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc,ENNReal.toReal_ofReal hh.le,smul_eq_mul]
  field_simp

include hW hWm in
omit [IsProbabilityMeasure μ] in
/-- The literal expected integrated energy is exactly a/(T-a). -/
theorem expected_energy (a T : ℝ≥0) (ha : a<T) :
    (∫ ω,(∫ t in Ioc 0 (T:ℝ), ‖control (W:=W) a T t.toNNReal ω‖^2) ∂μ)=
      (a:ℝ)/((T:ℝ)-a) := by
  simp_rw [sample_energy a T ha]
  rw [integral_div,CommonItoIsometry.integral_eval_sq hW hWm a]

end LinearStochastic.ScalarGramianEnergy
