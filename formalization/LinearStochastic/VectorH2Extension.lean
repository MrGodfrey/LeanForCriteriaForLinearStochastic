import LinearStochastic.CommonH2Extension
import LinearStochastic.LpOrthonormalCoordinates
import LinearStochastic.VectorHorizonRestriction

/-! Finite-dimensional Hilbert zero extension with the true Hilbert L² norm,
obtained by actual orthonormal coordinate reconstruction and Parseval. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.VectorH2Extension
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal InnerProductSpace BigOperators
open CommonItoL2 CommonItoCLM CommonVectorPicard CommonItoMultichannel
open LpOrthonormalCoordinates VectorItoProduct
section Lift
variable {Λ Γ E κ : Type*} {mΛ : MeasurableSpace Λ} {mΓ : MeasurableSpace Γ}
  {ν : Measure Λ} {ν' : Measure Γ} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype κ]
  (b : OrthonormalBasis κ ℝ E)

theorem norm_sq_coordinates (f : Lp E 2 ν) : ‖f‖^2 = ∑ k, ‖coordinate b k f‖^2 := by
  simpa only [real_inner_self_eq_norm_sq] using (coordinate_inner_sum b f f).symm

/-- The actual finite orthonormal tensor lift of a scalar linear map. -/
def liftLinear (L : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν') : Lp E 2 ν →ₗ[ℝ] Lp E 2 ν' where
  toFun f := assemble b (fun k ↦ L (coordinate b k f))
  map_add' f g := by
    simp only [assemble,coordinate,←ContinuousLinearMap.compLpₗ_apply,map_add,Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [assemble,coordinate,←ContinuousLinearMap.compLpₗ_apply,map_smul,Finset.smul_sum,RingHom.id_apply]

theorem coordinate_lift (L : Lp ℝ 2 ν →ₗ[ℝ] Lp ℝ 2 ν') (f : Lp E 2 ν) (k : κ) :
    coordinate b k (liftLinear b L f) = L (coordinate b k f) := coordinate_assemble b _ k

/-- Isometry is preserved in the true Hilbert norm, not the coordinate maximum. -/
def liftIsometry (L : Lp ℝ 2 ν →ₗᵢ[ℝ] Lp ℝ 2 ν') : Lp E 2 ν →ₗᵢ[ℝ] Lp E 2 ν' where
  toLinearMap := liftLinear b L.toLinearMap
  norm_map' f := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq_coordinates b,norm_sq_coordinates b]
    apply Finset.sum_congr rfl
    intro k _
    rw [coordinate_lift]
    exact congrArg (fun x : ℝ ↦ x^2) (L.norm_map _)

theorem lift_norm_le (L : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν') (hL : ∀ f, ‖L f‖ ≤ ‖f‖)
    (f : Lp E 2 ν) : ‖liftLinear b L.toLinearMap f‖ ≤ ‖f‖ := by
  have hsq : ‖liftLinear b L.toLinearMap f‖^2 ≤ ‖f‖^2 := by
    rw [norm_sq_coordinates b,norm_sq_coordinates b]
    apply Finset.sum_le_sum
    intro k _
    rw [coordinate_lift]
    exact pow_le_pow_left₀ (norm_nonneg _) (hL _) 2
  nlinarith [norm_nonneg (liftLinear b L.toLinearMap f),norm_nonneg f]
end Lift
variable {Ω E κ : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype κ]
  (b : OrthonormalBasis κ ℝ E) {W : ℝ≥0 → Ω → ℝ}
  [CommonItoIsometry.ForwardIndependent W 𝓕 μ] (hWm : ∀ t, Measurable (W t))

/-- Actual vector zero extension of a restarted control to a containing horizon. -/
def extendShift (a δ T : ℝ≥0) (h : a+δ ≤ T) :
    Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ) →ₗᵢ[ℝ]
      Lp E 2 (spacetimeMeasure 𝓕 μ T) := liftIsometry b (CommonH2Extension.extendShift hWm a δ T h)

theorem extendShift_norm (a δ T : ℝ≥0) (h : a+δ ≤ T)
    (g : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ)) :
    ‖extendShift b hWm a δ T h g‖ = ‖g‖ := (extendShift b hWm a δ T h).norm_map g

theorem coordinate_extendShift (a δ T : ℝ≥0) (h : a+δ ≤ T)
    (g : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ)) (k : κ) :
    coordinate b k (extendShift b hWm a δ T h g) =
      CommonH2Extension.extendShift hWm a δ T h (coordinate b k g) := coordinate_assemble (mΛ:=𝓕.predictable) b _ k

/-- The actual vector translation map is obtained from the same scalar
translation, and is a continuous contraction. -/
def shift (a δ T : ℝ≥0) (h : a+δ ≤ T) :
    Lp E 2 (spacetimeMeasure 𝓕 μ T) →L[ℝ]
      Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ) :=
  (liftLinear b (CommonShiftH2.shiftCLM a δ T h).toLinearMap).mkContinuous 1 (fun f ↦ by
    simpa only [one_mul] using lift_norm_le b (CommonShiftH2.shiftCLM a δ T h)
      (CommonShiftH2.shift_norm a δ T h) f)

theorem shift_extendShift (a δ T : ℝ≥0) (h : a+δ ≤ T)
    (g : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ)) :
    shift b a δ T h (extendShift b hWm a δ T h g) = g := by
  have he : (fun k ↦ CommonShiftH2.shiftCLM a δ T h
      (coordinate b k (extendShift b hWm a δ T h g))) = fun k ↦ coordinate b k g := by
    funext k
    rw [coordinate_extendShift]
    exact CommonH2Extension.shift_extendShift hWm a δ T h _
  change assemble (mΛ:=(CommonTimeShift.filtration 𝓕 a).predictable) b _ = g
  exact (congrArg (assemble (mΛ:=(CommonTimeShift.filtration 𝓕 a).predictable) b) he).trans (assemble_coordinates (mΛ:=(CommonTimeShift.filtration 𝓕 a).predictable) b g)

/-- The vector translation is represented by the actual deterministic shift. -/
theorem shift_ae (a δ T : ℝ≥0) (h : a+δ ≤ T)
    (f : Lp E 2 (spacetimeMeasure 𝓕 μ T)) :
    (shift b a δ T h f : ℝ≥0 × Ω → E) =ᵐ[(timeMeasure_T δ).prod μ]
      fun z ↦ f (a+z.1,z.2) := by
  have hk : ∀ᵐ z ∂(timeMeasure_T δ).prod μ, ∀ k,
      CommonShiftH2.shiftCLM a δ T h (coordinate b k f) z = inner ℝ (b k) (f (a+z.1,z.2)) := by
    rw [ae_all_iff]
    intro k
    have hc : (coordinate b k f : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ]
        fun z ↦ inner ℝ (b k) (f z) := ae_of_ae_trim 𝓕.predictable_le_prod (coordinate_ae b k f)
    exact (CommonShiftH2.shift_ae a δ T h (coordinate b k f)).trans (CommonShiftH2.pull_ae a δ T h hc)
  have ha : (shift b a δ T h f : ℝ≥0 × Ω → E) =ᵐ[(timeMeasure_T δ).prod μ]
      fun z ↦ ∑ k, (CommonShiftH2.shiftCLM a δ T h (coordinate b k f)) z • b k :=
    ae_of_ae_trim (CommonTimeShift.filtration 𝓕 a).predictable_le_prod (assemble_ae (mΛ:=(CommonTimeShift.filtration 𝓕 a).predictable) b _)
  filter_upwards [ha,hk] with z ha hk
  rw [ha]
  simpa only [hk] using b.sum_repr' (f (a+z.1,z.2))

/-- An almost-everywhere property on the local interval pulls back to its
actual window in any containing global horizon. -/
theorem window_ae (a δ T : ℝ≥0) (h : a+δ ≤ T) (p : ℝ≥0 × Ω → Prop)
    (hp : ∀ᵐ z ∂(timeMeasure_T δ).prod μ, p z) :
    ∀ᵐ z ∂(timeMeasure_T T).prod μ, a < z.1 ∧ z.1 ≤ a+δ → p (z.1-a,z.2) := by
  have hs := ((CommonH2Paste.sub_interval a δ).prod (MeasurePreserving.id μ)).quasiMeasurePreserving.ae hp
  have hm : (timeMeasure.restrict (Ioc a (a+δ))).prod μ =
      ((timeMeasure_T T).prod μ).restrict {z | a < z.1 ∧ z.1 ≤ a+δ} := by
    have hh := Measure.restrict_prod_eq_prod_univ (μ:=timeMeasure_T T) (ν:=μ) (Ioc a (a+δ))
    have hset : Ioc a (a+δ) ×ˢ (univ : Set Ω) = {z | a < z.1 ∧ z.1 ≤ a+δ} := by ext z; simp
    rw [hset] at hh
    rw [←hh]
    congr 1
    change timeMeasure.restrict (Ioc a (a+δ)) = (timeMeasure.restrict (Ioc 0 T)).restrict (Ioc a (a+δ))
    rw [Measure.restrict_restrict measurableSet_Ioc]
    congr 1
    have hsub : Ioc a (a+δ) ⊆ Ioc (0:ℝ≥0) T := fun t ht ↦ ⟨lt_of_le_of_lt zero_le ht.1,ht.2.trans h⟩
    exact (inter_eq_left.mpr hsub).symm
  have hs' := hs.filter_mono (ae_mono hm.ge)
  exact (ae_restrict_iff' (measurable_fst measurableSet_Ioc)).mp hs'

/-- The actual vector representative is exactly the input translated onto its
window, with zero on both complementary time pieces. -/
theorem extendShift_ae (a δ T : ℝ≥0) (h : a+δ ≤ T)
    (g : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ)) :
    (extendShift b hWm a δ T h g : ℝ≥0 × Ω → E) =ᵐ[(timeMeasure_T T).prod μ]
      fun z ↦ if a < z.1 ∧ z.1 ≤ a+δ then g (z.1-a,z.2) else 0 := by
  have hk : ∀ᵐ z ∂(timeMeasure_T T).prod μ, ∀ k,
      CommonH2Extension.extendShift hWm a δ T h (coordinate b k g) z =
        if a < z.1 ∧ z.1 ≤ a+δ then inner ℝ (b k) (g (z.1-a,z.2)) else 0 := by
    rw [ae_all_iff]
    intro k
    have hc : (coordinate b k g : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T δ).prod μ]
        fun z ↦ inner ℝ (b k) (g z) :=
      ae_of_ae_trim (CommonTimeShift.filtration 𝓕 a).predictable_le_prod (coordinate_ae b k g)
    have hw := window_ae a δ T h (fun z ↦ coordinate b k g z = inner ℝ (b k) (g z)) hc
    filter_upwards [CommonH2Extension.extendShift_ae hWm a δ T h (coordinate b k g),hw] with z he hw
    rw [he]
    split_ifs with ht
    · exact hw ht
    · rfl
  have ha : (extendShift b hWm a δ T h g : ℝ≥0 × Ω → E) =ᵐ[(timeMeasure_T T).prod μ]
      fun z ↦ ∑ k, CommonH2Extension.extendShift hWm a δ T h (coordinate b k g) z • b k :=
    ae_of_ae_trim 𝓕.predictable_le_prod (assemble_ae (mΛ:=𝓕.predictable) b _)
  filter_upwards [ha,hk] with z ha hk
  rw [ha]
  by_cases ht : a < z.1 ∧ z.1 ≤ a+δ
  · simp only [hk,if_pos ht]
    exact b.sum_repr' _
  · simp only [hk,if_neg ht,zero_smul,Finset.sum_const_zero]

/-- Every vector prefix before the window is exactly zero. -/
theorem restriction_extendShift_zero (a δ T t : ℝ≥0) (h : a+δ ≤ T) (ht : t ≤ a)
    (g : Lp E 2 (spacetimeMeasure (CommonTimeShift.filtration 𝓕 a) μ δ)) :
    VectorHorizonRestriction.restrict (ht.trans ((le_add_right le_rfl).trans h))
      (extendShift b hWm a δ T h g) = 0 := by
  apply Lp.ext
  apply (Lp.stronglyMeasurable _).ae_eq_trim_of_stronglyMeasurable 𝓕.predictable_le_prod (Lp.stronglyMeasurable _)
  have hm : (timeMeasure_T t).prod μ ≤ (timeMeasure_T T).prod μ :=
    Measure.prod_mono (Measure.restrict_mono (Ioc_subset_Ioc_right (ht.trans ((le_add_right le_rfl).trans h))) le_rfl) le_rfl
  have hs : ∀ᵐ s ∂timeMeasure_T t, s ≤ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs using hs.2
  filter_upwards [ae_of_ae_trim 𝓕.predictable_le_prod (VectorHorizonRestriction.restrict_ae (ht.trans ((le_add_right le_rfl).trans h)) (extendShift b hWm a δ T h g)),
    (extendShift_ae b hWm a δ T h g).filter_mono (ae_mono hm),
    ae_of_ae_trim 𝓕.predictable_le_prod (Lp.coeFn_zero E 2 (spacetimeMeasure 𝓕 μ t)),
    Measure.quasiMeasurePreserving_fst.ae hs] with z hr he hz hs
  rw [hr,he,hz]
  exact if_neg (fun hh ↦ (not_lt_of_ge (hs.trans ht)) hh.1)
end LinearStochastic.VectorH2Extension
