import LinearStochastic.CommonH2Split

/-! Genuine isometric extension of predictable controls by zero outside a
finite deterministic interval, with exact restriction and restart identities. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.CommonH2Extension
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonShiftH2 CommonH2Paste CommonHorizonRestriction CommonH2Split
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent W 𝓕 μ] (hWm : ∀ t, Measurable (W t))

/-- Zero extension to a later endpoint is a genuine linear isometry. -/
def left (a δ : ℝ≥0) : H2 𝓕 μ a →ₗᵢ[ℝ] H2 𝓕 μ (a+δ) where
  toFun f := pasteH2 a δ f 0
  map_add' f g := by simpa only [add_zero] using paste_add hWm a δ f g 0 0
  map_smul' c f := by simpa only [smul_zero,RingHom.id_apply] using paste_smul hWm a δ c f 0
  norm_map' f := by
    have hh := paste_norm_sq hWm a δ f 0
    simp only [norm_zero,zero_pow (by decide : 2≠0),add_zero] at hh
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hh

/-- Translating a restarted control after a zero prefix is isometric. -/
def right (a δ : ℝ≥0) : H2 (CommonTimeShift.filtration 𝓕 a) μ δ →ₗᵢ[ℝ] H2 𝓕 μ (a+δ) where
  toFun g := pasteH2 a δ 0 g
  map_add' f g := by simpa only [zero_add] using paste_add hWm a δ 0 0 f g
  map_smul' c f := by simpa only [smul_zero,RingHom.id_apply] using paste_smul hWm a δ c 0 f
  norm_map' f := by
    have hh := paste_norm_sq hWm a δ 0 f
    simp only [norm_zero,zero_pow (by decide : 2≠0),zero_add] at hh
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hh

/-- Pasting respects the actual almost-everywhere representatives on both pieces. -/
theorem paste_congr_ae (a δ : ℝ≥0) (R R' S S' : ℝ≥0 → Ω → ℝ)
    (hR : Function.uncurry R =ᵐ[(timeMeasure_T a).prod μ] Function.uncurry R')
    (hS : Function.uncurry S =ᵐ[(timeMeasure_T δ).prod μ] Function.uncurry S') :
    Function.uncurry (CommonProcessPaste.paste a R S) =ᵐ[(timeMeasure_T (a+δ)).prod μ]
      Function.uncurry (CommonProcessPaste.paste a R' S') := by
  rw [time_split,Measure.add_prod]
  change (∀ᵐ z ∂(timeMeasure_T a).prod μ+(timeMeasure.restrict (Ioc a (a+δ))).prod μ,
    Function.uncurry (CommonProcessPaste.paste a R S) z = Function.uncurry (CommonProcessPaste.paste a R' S') z)
  rw [ae_add_measure_iff]
  constructor
  · have ht : ∀ᵐ t ∂timeMeasure_T a, t ≤ a := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using ht.2
    filter_upwards [hR,Measure.quasiMeasurePreserving_fst.ae ht] with z hz ht
    exact (if_pos ht).trans (hz.trans (if_pos ht).symm)
  · have hs := ((sub_interval a δ).prod (MeasurePreserving.id μ)).quasiMeasurePreserving.ae hS
    have ht : ∀ᵐ t ∂timeMeasure.restrict (Ioc a (a+δ)), ¬t ≤ a := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using not_le_of_gt ht.1
    filter_upwards [hs,Measure.quasiMeasurePreserving_fst.ae ht] with z hz ht
    exact (if_neg ht).trans (hz.trans (if_neg ht).symm)

theorem left_ae (a δ : ℝ≥0) (f : H2 𝓕 μ a) :
    (left hWm a δ f : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T (a+δ)).prod μ]
      fun z ↦ if z.1 ≤ a then f z else 0 := by
  exact (pasteH2_ae a δ f 0).trans (paste_congr_ae a δ
    (fun t ω ↦ f (t,ω)) (fun t ω ↦ f (t,ω))
    (fun t ω ↦ (0 : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) (t,ω)) (fun _ _ ↦ 0)
    Filter.EventuallyEq.rfl
    (ae_of_ae_trim (CommonTimeShift.filtration 𝓕 a).predictable_le_prod (Lp.coeFn_zero ℝ 2 _)))

theorem right_ae (a δ : ℝ≥0) (g : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) :
    (right hWm a δ g : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T (a+δ)).prod μ]
      fun z ↦ if z.1 ≤ a then 0 else g (z.1-a,z.2) := by
  exact (pasteH2_ae a δ 0 g).trans (paste_congr_ae a δ
    (fun t ω ↦ (0 : H2 𝓕 μ a) (t,ω)) (fun _ _ ↦ 0)
    (fun t ω ↦ g (t,ω)) (fun t ω ↦ g (t,ω))
    (ae_of_ae_trim 𝓕.predictable_le_prod (Lp.coeFn_zero ℝ 2 _)) Filter.EventuallyEq.rfl)

/-- A true equality of time horizons changes neither raw functions nor norms. -/
def castH2 {s t : ℝ≥0} (h : s=t) : H2 𝓕 μ s →ₗᵢ[ℝ] H2 𝓕 μ t := by
  subst t
  exact LinearIsometry.id

omit [IsProbabilityMeasure μ] in
theorem castH2_apply {s t : ℝ≥0} (h : s=t) (f : H2 𝓕 μ s) :
    (castH2 h f : ℝ≥0 × Ω → ℝ) = f := by
  subst t
  rfl

/-- Exact isometric zero extension to any containing horizon. -/
def extendShift (a δ T : ℝ≥0) (h : a+δ ≤ T) :
    H2 (CommonTimeShift.filtration 𝓕 a) μ δ →ₗᵢ[ℝ] H2 𝓕 μ T :=
  (castH2 (add_tsub_cancel_of_le h)).comp
    ((left hWm (a+δ) (T-(a+δ))).comp (right hWm a δ))

theorem extendShift_norm (a δ T : ℝ≥0) (h : a+δ ≤ T)
    (g : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) :
    ‖extendShift hWm a δ T h g‖ = ‖g‖ := (extendShift hWm a δ T h).norm_map g

/-- The actual ambient representative is exactly the translated input on the
half-open window and zero elsewhere. Boundary values carry no time mass. -/
theorem extendShift_ae (a δ T : ℝ≥0) (h : a+δ ≤ T)
    (g : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) :
    (extendShift hWm a δ T h g : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ]
      fun z ↦ if a < z.1 ∧ z.1 ≤ a+δ then g (z.1-a,z.2) else 0 := by
  let q := right hWm a δ g
  let r := T-(a+δ)
  have he : (a+δ)+r=T := add_tsub_cancel_of_le h
  have hcast : (extendShift hWm a δ T h g : ℝ≥0 × Ω → ℝ) = left hWm (a+δ) r q := by
    dsimp only [extendShift,LinearIsometry.comp_apply]
    exact castH2_apply (𝓕:=𝓕) (μ:=μ) he (left hWm (a+δ) r q)
  rw [hcast]
  have hleft := left_ae hWm (a+δ) r q
  have hme : (timeMeasure_T ((a+δ)+r)).prod μ = (timeMeasure_T T).prod μ := congrArg (fun s ↦ (timeMeasure_T s).prod μ) he
  have hleftT := hleft.filter_mono (ae_mono hme.ge)
  have hright := right_ae hWm a δ g
  have hright' : ∀ᵐ z ∂(timeMeasure_T T).prod μ, z.1 ≤ a+δ →
      q z = if z.1 ≤ a then 0 else g (z.1-a,z.2) := by
    have hm : (timeMeasure_T (a+δ)).prod μ =
        ((timeMeasure_T T).prod μ).restrict {z | z.1 ≤ a+δ} := by
      have hp := Measure.restrict_prod_eq_prod_univ (μ:=timeMeasure_T T) (ν:=μ) (Iic (a+δ))
      have hset : (Iic (a+δ)) ×ˢ (univ : Set Ω) = {z | z.1 ≤ a+δ} := by ext z; simp
      rw [hset] at hp
      rw [←hp]
      congr 1
      change timeMeasure.restrict (Ioc 0 (a+δ)) =
        (timeMeasure.restrict (Ioc 0 T)).restrict (Iic (a+δ))
      rw [Measure.restrict_restrict measurableSet_Iic]
      congr 1
      ext t
      simp only [mem_inter_iff,mem_Iic,mem_Ioc]
      constructor
      · intro ht; exact ⟨ht.2,ht.1,ht.2.trans h⟩
      · intro ht; exact ⟨ht.2.1,ht.1⟩
    have hrightOn := hright.filter_mono (ae_mono hm.ge)
    have hz := (ae_restrict_iff' (measurable_fst measurableSet_Iic)).mp hrightOn
    filter_upwards [hz] with z hz
    intro ht
    exact hz ht
  filter_upwards [hleftT,hright'] with z hl hr
  change (left hWm (a+δ) r q : ℝ≥0 × Ω → ℝ) z = _ at hl
  rw [hl]
  by_cases ht : z.1 ≤ a+δ
  · rw [if_pos ht,hr ht]
    by_cases hs : z.1 ≤ a
    · simp [hs,not_lt_of_ge hs]
    · simp [hs,lt_of_not_ge hs,ht]
  · simp [ht]
/-- Restarting the actual zero extension recovers the supplied local control. -/
theorem shift_extendShift (a δ T : ℝ≥0) (h : a+δ ≤ T)
    (g : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) :
    shiftCLM a δ T h (extendShift hWm a δ T h g) = g := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable
    (CommonTimeShift.filtration 𝓕 a).predictable_le_prod (Lp.stronglyMeasurable _)
  have ht : ∀ᵐ t ∂timeMeasure_T δ, 0 < t ∧ t ≤ δ := ae_restrict_mem measurableSet_Ioc
  filter_upwards [shift_ae a δ T h (extendShift hWm a δ T h g),
    pull_ae a δ T h (extendShift_ae hWm a δ T h g),Measure.quasiMeasurePreserving_fst.ae ht]
    with z hs he ht
  exact hs.trans (he.trans (by
    rw [if_pos ⟨lt_add_of_pos_right a ht.1,add_le_add_right ht.2 a⟩,add_tsub_cancel_left]))

/-- Every prefix ending before the window is exactly the zero class. -/
theorem restriction_extendShift_zero (a δ T t : ℝ≥0) (h : a+δ ≤ T) (ht : t ≤ a)
    (g : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) :
    restriction hWm (ht.trans ((le_add_right le_rfl).trans h)) (extendShift hWm a δ T h g) = 0 := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable 𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
  have hm : (timeMeasure_T t).prod μ ≤ (timeMeasure_T T).prod μ :=
    Measure.prod_mono (Measure.restrict_mono (Ioc_subset_Ioc_right (ht.trans ((le_add_right le_rfl).trans h))) le_rfl) le_rfl
  have hs : ∀ᵐ s ∂timeMeasure_T t, s ≤ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs using hs.2
  filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod (restriction_ae hWm _ (extendShift hWm a δ T h g)),
    (extendShift_ae hWm a δ T h g).filter_mono (ae_mono hm),
    ae_of_ae_trim 𝓕.predictable_le_prod (Lp.coeFn_zero ℝ 2 (CommonItoMultichannel.spacetimeMeasure 𝓕 μ t)),
    Measure.quasiMeasurePreserving_fst.ae hs] with z hr he hz hs
  rw [hr,he,hz]
  exact if_neg (fun hh ↦ (not_lt_of_ge (hs.trans ht)) hh.1)

/-- Enlarging the containing horizon does not change the actual window control. -/
theorem restriction_extendShift (a δ s T : ℝ≥0) (hs : a+δ ≤ s) (hT : s ≤ T)
    (g : H2 (CommonTimeShift.filtration 𝓕 a) μ δ) :
    restriction hWm hT (extendShift hWm a δ T (hs.trans hT) g) = extendShift hWm a δ s hs g := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable 𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
  have hm : (timeMeasure_T s).prod μ ≤ (timeMeasure_T T).prod μ :=
    Measure.prod_mono (Measure.restrict_mono (Ioc_subset_Ioc_right hT) le_rfl) le_rfl
  have hr : (restriction hWm hT (extendShift hWm a δ T (hs.trans hT) g) : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T s).prod μ]
      (extendShift hWm a δ T (hs.trans hT) g) :=
    ae_of_ae_trim 𝓕.predictable_le_prod (restriction_ae hWm hT _)
  exact hr.trans
    (((extendShift_ae hWm a δ T (hs.trans hT) g).filter_mono (ae_mono hm)).trans
      (extendShift_ae hWm a δ s hs g).symm)
end LinearStochastic.CommonH2Extension
