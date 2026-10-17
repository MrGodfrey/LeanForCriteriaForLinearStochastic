module

public import LinearStochastic.CommonStateS2

@[expose] public section

/-! Quantitative real-valued S² norms of actual paths, including triangle,
finite-sum and interval-pasting bounds for the true uncountable supremum. -/
noncomputable section
namespace LinearStochastic.PathSupNorm
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators
open ContinuousDoobL2
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup E]

def norm (X : ℝ≥0 → Ω → E) (T : ℝ≥0) : ℝ :=
  (eLpNorm (pathSup X T) 2 μ).toReal

theorem nonneg (X : ℝ≥0 → Ω → E) (T : ℝ≥0) : 0 ≤ norm (μ:=μ) X T := ENNReal.toReal_nonneg

theorem congr (T : ℝ≥0) {X Y : ℝ≥0 → Ω → E}
    (h : ∀ᵐ ω ∂μ, ∀ t, t≤T → X t ω=Y t ω) : norm (μ:=μ) X T=norm (μ:=μ) Y T := by
  unfold norm
  rw [eLpNorm_congr_ae (CommonDriftS2.pathSup_congr T h)]

theorem constant (T : ℝ≥0) (ξ : Ω → E) (hξ : MemLp ξ 2 μ) :
    norm (μ:=μ) (fun _=>ξ) T=‖hξ.toLp ξ‖ := by
  letI : Nonempty (Iic T) := ⟨⟨T,show T≤T from le_rfl⟩⟩
  rw [Lp.norm_toLp]
  change (eLpNorm (fun ω => ⨆ _ : Iic T, ‖ξ ω‖) 2 μ).toReal = _
  simp only [ciSup_const,eLpNorm_norm ξ hξ.aestronglyMeasurable]

/-- The real S² norm is exactly the expected squared supremum after squaring. -/
theorem sq_eq_integral (T : ℝ≥0) (X : ℝ≥0 → Ω → E)
    (h2 : MemLp (pathSup X T) 2 μ) :
    norm (μ:=μ) X T ^ 2 = ∫ ω, pathSup X T ω ^ 2 ∂μ := by
  rw [norm,←Lp.norm_toLp _ h2,CommonItoL2.lp_two_norm_sq]
  apply integral_congr_ae
  filter_upwards [h2.coeFn_toLp] with ω hω
  rw [hω]

omit mΩ in
/-- Pointwise triangle for the actual supremum; continuity supplies the
boundedness needed for real conditional suprema. -/
theorem sup_add (T : ℝ≥0) (X Y : ℝ≥0 → Ω → E) (ω : Ω)
    (hX : ContinuousOn (fun t=>X t ω) (Iic T)) (hY : ContinuousOn (fun t=>Y t ω) (Iic T)) :
    pathSup (fun t ω=>X t ω+Y t ω) T ω ≤ pathSup X T ω+pathSup Y T ω := by
  have hc : IsCompact (Iic T) := by rw [←Icc_bot]; exact isCompact_Icc
  have hbX : BddAbove (range (fun t : Iic T=>‖X t.val ω‖)) := by
    simpa only [image_eq_range] using hc.bddAbove_image hX.norm
  have hbY : BddAbove (range (fun t : Iic T=>‖Y t.val ω‖)) := by
    simpa only [image_eq_range] using hc.bddAbove_image hY.norm
  apply ciSup_le
  intro t
  exact (norm_add_le _ _).trans (add_le_add (le_ciSup hbX t) (le_ciSup hbY t))

/-- Minkowski for actual continuous S² paths. -/
theorem add_le (T : ℝ≥0) (X Y : ℝ≥0 → Ω → E)
    (hX : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>X t ω) (Iic T))
    (hY : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>Y t ω) (Iic T))
    (hX2 : MemLp (pathSup X T) 2 μ) (hY2 : MemLp (pathSup Y T) 2 μ) :
    norm (μ:=μ) (fun t ω=>X t ω+Y t ω) T ≤ norm (μ:=μ) X T+norm (μ:=μ) Y T := by
  by_cases hm : AEStronglyMeasurable (pathSup (fun t ω=>X t ω+Y t ω) T) μ
  swap
  · simpa only [norm, eLpNorm_of_not_aestronglyMeasurable hm, ENNReal.toReal_top] using
      (add_nonneg (nonneg (μ:=μ) X T) (nonneg (μ:=μ) Y T))
  have he : eLpNorm (pathSup (fun t ω=>X t ω+Y t ω) T) 2 μ ≤
      eLpNorm (pathSup X T) 2 μ+eLpNorm (pathSup Y T) 2 μ := by
    apply (eLpNorm_mono_ae_real (g:=fun ω=>pathSup X T ω+pathSup Y T ω) hm ?_).trans
      (eLpNorm_add_le (by norm_num : (1:ℝ≥0∞)≤2))
    filter_upwards [hX,hY] with ω hx hy
    have hn : 0≤pathSup (fun t ω=>X t ω+Y t ω) T ω := Real.iSup_nonneg (fun _=>norm_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg hn]
    exact sup_add T X Y ω hx hy
  have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hX2.eLpNorm_lt_top.ne,hY2.eLpNorm_lt_top.ne⟩) he
  simpa only [norm,ENNReal.toReal_add hX2.eLpNorm_lt_top.ne hY2.eLpNorm_lt_top.ne] using hh

/-- Finite sums of actual adapted continuous paths obey the corresponding
sum of S² norms. -/
theorem sum_le {𝓕 : Filtration ℝ≥0 mΩ}
    {ι : Type*} (s : Finset ι) (T : ℝ≥0)
    (X : ι → ℝ≥0 → Ω → E)
    (ha : ∀ i∈s, StronglyAdapted 𝓕 (X i))
    (hc : ∀ i∈s, ∀ᵐ ω ∂μ, ContinuousOn (fun t=>X i t ω) (Iic T))
    (h2 : ∀ i∈s, MemLp (pathSup (X i) T) 2 μ) :
    norm (μ:=μ) (fun t ω=>∑ i∈s, X i t ω) T ≤ ∑ i∈s, norm (μ:=μ) (X i) T := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change (eLpNorm (fun ω => ⨆ _ : Iic T, ‖(0:E)‖) 2 μ).toReal ≤ 0
    simp
  | @insert i s hi ih =>
    have hsa : ∀ j∈s, StronglyAdapted 𝓕 (X j) := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hsc : ∀ j∈s, ∀ᵐ ω ∂μ, ContinuousOn (fun t=>X j t ω) (Iic T) :=
      fun j hj=>hc j (Finset.mem_insert_of_mem hj)
    have hs2 : ∀ j∈s, MemLp (pathSup (X j) T) 2 μ := fun j hj=>h2 j (Finset.mem_insert_of_mem hj)
    have hsumc : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>∑ j∈s, X j t ω) (Iic T) := by
      have hall := (ae_ball_iff s.countable_toSet).mpr hsc
      filter_upwards [hall] with ω hω
      exact continuousOn_finsetSum s hω
    simp only [Finset.sum_insert hi]
    exact (add_le T (X i) (fun t ω=>∑ j∈s, X j t ω)
      (hc i (Finset.mem_insert_self _ _)) hsumc
      (h2 i (Finset.mem_insert_self _ _))
      (CommonStateS2.pathSup_sum_memLp s T X hsa hsc hs2)).trans
      (add_le_add le_rfl (ih hsa hsc hs2))

/-- Evaluation at an actual time is bounded by the full-path S² norm. -/
theorem eval_le (T t : ℝ≥0) (ht : t≤T) (X : ℝ≥0 → Ω → E)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>X t ω) (Iic T))
    (h2 : MemLp (pathSup X T) 2 μ) :
    (eLpNorm (X t) 2 μ).toReal ≤ norm (μ:=μ) X T := by
  by_cases hm : AEStronglyMeasurable (X t) μ
  swap
  · simpa only [eLpNorm_of_not_aestronglyMeasurable hm, ENNReal.toReal_top] using
      (nonneg (μ:=μ) X T)
  apply ENNReal.toReal_mono h2.eLpNorm_lt_top.ne
  apply eLpNorm_mono_ae_real hm
  filter_upwards [hc] with ω hω
  have hcompact : IsCompact (Iic T) := by rw [←Icc_bot]; exact isCompact_Icc
  have hb : BddAbove (range (fun s : Iic T=>‖X s.val ω‖)) := by
    simpa only [image_eq_range] using hcompact.bddAbove_image hω.norm
  exact le_ciSup hb ⟨t,ht⟩

/-- The full-interval supremum is bounded by the two actual adjacent pieces.
This compares the same path, with a literal time translation on the second piece. -/
theorem split_le (a δ : ℝ≥0) (X : ℝ≥0 → Ω → E)
    (hpre : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>X t ω) (Iic a))
    (hpost : ∀ᵐ ω ∂μ, ContinuousOn (fun t=>X (a+t) ω) (Iic δ))
    (hpre2 : MemLp (pathSup X a) 2 μ)
    (hpost2 : MemLp (pathSup (fun t ω=>X (a+t) ω) δ) 2 μ) :
    norm (μ:=μ) X (a+δ) ≤ norm (μ:=μ) X a+norm (μ:=μ) (fun t ω=>X (a+t) ω) δ := by
  by_cases hm : AEStronglyMeasurable (pathSup X (a+δ)) μ
  swap
  · simpa only [norm, eLpNorm_of_not_aestronglyMeasurable hm, ENNReal.toReal_top] using
      (add_nonneg (nonneg (μ:=μ) X a) (nonneg (μ:=μ) (fun t ω=>X (a+t) ω) δ))
  have he : eLpNorm (pathSup X (a+δ)) 2 μ ≤
      eLpNorm (pathSup X a) 2 μ+eLpNorm (pathSup (fun t ω=>X (a+t) ω) δ) 2 μ := by
    apply (eLpNorm_mono_ae_real (g:=fun ω=>pathSup X a ω+pathSup (fun t ω=>X (a+t) ω) δ ω) hm ?_).trans
      (eLpNorm_add_le (by norm_num : (1:ℝ≥0∞)≤2))
    filter_upwards [hpre,hpost] with ω hp hq
    have hcomp (t : ℝ≥0) : IsCompact (Iic t) := by rw [←Icc_bot]; exact isCompact_Icc
    have hbpre : BddAbove (range (fun t : Iic a=>‖X t.val ω‖)) := by
      simpa only [image_eq_range] using (hcomp a).bddAbove_image hp.norm
    have hbpost : BddAbove (range (fun t : Iic δ=>‖X (a+t.val) ω‖)) := by
      simpa only [image_eq_range] using (hcomp δ).bddAbove_image hq.norm
    have hn : 0≤pathSup X (a+δ) ω := Real.iSup_nonneg (fun _=>norm_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg hn]
    apply ciSup_le
    intro t
    by_cases ht : t.val≤a
    · exact (le_ciSup hbpre ⟨t.val,ht⟩).trans
        (le_add_of_nonneg_right (Real.iSup_nonneg (fun _=>norm_nonneg _)))
    · have ha : a≤t.val := le_of_not_ge ht
      have hd : t.val-a≤δ := tsub_le_iff_right.mpr (by simpa only [add_comm] using (show t.val≤a+δ from t.property))
      have hv := le_ciSup hbpost ⟨t.val-a,hd⟩
      rw [add_tsub_cancel_of_le ha] at hv
      exact hv.trans (le_add_of_nonneg_left (Real.iSup_nonneg (fun _=>norm_nonneg _)))
  have hh := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hpre2.eLpNorm_lt_top.ne,hpost2.eLpNorm_lt_top.ne⟩) he
  simpa only [norm,ENNReal.toReal_add hpre2.eLpNorm_lt_top.ne hpost2.eLpNorm_lt_top.ne] using hh

omit mΩ in
/-- The square of the actual path supremum equals the supremum of squared
norms. Compactness of the closed time interval supplies an attained maximum. -/
theorem square_sup (T : ℝ≥0) (X : ℝ≥0 → Ω → E) (ω : Ω)
    (hc : ContinuousOn (fun t=>X t ω) (Iic T)) :
    (⨆ t : Iic T, ‖X t.val ω‖^2)=pathSup X T ω^2 := by
  have hcomp : IsCompact (Iic T) := by rw [←Icc_bot]; exact isCompact_Icc
  obtain ⟨t,ht,hmax⟩ := hcomp.exists_isMaxOn ⟨T,by simp⟩ hc.norm
  have hb : BddAbove (range (fun s : Iic T=>‖X s.val ω‖)) := by
    simpa only [image_eq_range] using hcomp.bddAbove_image hc.norm
  have hb2 : BddAbove (range (fun s : Iic T=>‖X s.val ω‖^2)) := by
    simpa only [image_eq_range,Pi.pow_apply] using hcomp.bddAbove_image (hc.norm.pow 2)
  have he : pathSup X T ω=‖X t ω‖ :=
    le_antisymm (ciSup_le (fun s=>hmax s.property)) (le_ciSup hb ⟨t,ht⟩)
  rw [he]
  exact le_antisymm (ciSup_le (fun s=>(sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (hmax s.property))) (le_ciSup hb2 ⟨t,ht⟩)

end LinearStochastic.PathSupNorm
