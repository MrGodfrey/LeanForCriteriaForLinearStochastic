module

public import LinearStochastic.CommonDriftS2
public import LinearStochastic.CommonLocalSolution
public import LinearStochastic.CommonFiltrationCompletion

@[expose] public section

/-! Whole-path square integrability of the actual local state representative.
The deterministic drift is estimated by Cauchy–Schwarz, and only the actual
martingale term uses Doob. No S² estimate is assumed as a solution field. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonStateS2
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
open CommonVectorPicard CommonPicardRealization CommonDriftS2 ContinuousDoobL2
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ}

omit [IsProbabilityMeasure μ] in
/-- Countable dense maxima give measurability even with only almost surely
continuous paths on the closed horizon. -/
theorem pathSup_measurableOn {E : Type*} [NormedAddCommGroup E] (T : ℝ≥0) {X : ℝ≥0 → Ω → E}
    (ha : StronglyAdapted 𝓕 X)
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Iic T)) :
    AEStronglyMeasurable (pathSup X T) μ := by
  let Y : ℝ≥0 → Ω → E := fun t ↦ X (min t T)
  have hya : StronglyAdapted 𝓕 Y := fun t ↦ (ha (min t T)).mono (𝓕.mono (min_le_left t T))
  have hyc : ∀ᵐ ω ∂μ, Continuous (fun t ↦ Y t ω) := by
    filter_upwards [hc] with ω hω
    exact continuousOn_univ.mp (hω.comp
      (continuous_id.min continuous_const).continuousOn (fun t _ ↦ min_le_right t T))
  have he : pathSup X T = pathSup Y T := by
    funext ω
    unfold pathSup
    congr 1
    funext t
    simp only [Y,min_eq_left (show t.val ≤ T from t.property)]
  rw [he]
  exact pathSup_aestronglyMeasurable_ae hya hyc T

omit [IsProbabilityMeasure μ] in
/-- Addition preserves S² for actual adapted continuous processes. -/
theorem pathSup_add_memLp {E : Type*} [NormedAddCommGroup E] (T : ℝ≥0) {X Y : ℝ≥0 → Ω → E}
    (hXa : StronglyAdapted 𝓕 X) (hYa : StronglyAdapted 𝓕 Y)
    (hXc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω) (Iic T))
    (hYc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ Y t ω) (Iic T))
    (hX2 : MemLp (pathSup X T) 2 μ) (hY2 : MemLp (pathSup Y T) 2 μ) :
    MemLp (pathSup (fun t ω ↦ X t ω + Y t ω) T) 2 μ := by
  letI : Nonempty (Iic T) := ⟨⟨T,show T ≤ T from le_rfl⟩⟩
  have ha : StronglyAdapted 𝓕 (fun t ω ↦ X t ω + Y t ω) := fun t ↦ (hXa t).add (hYa t)
  have hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X t ω + Y t ω) (Iic T) := by
    filter_upwards [hXc,hYc] with ω hx hy using hx.add hy
  apply (hX2.add hY2).mono' (pathSup_measurableOn T ha hc)
  filter_upwards [hXc,hYc] with ω hx hy
  change |pathSup (fun t ω ↦ X t ω + Y t ω) T ω| ≤ _
  have hn : 0 ≤ pathSup (fun t ω ↦ X t ω + Y t ω) T ω :=
    Real.iSup_nonneg fun t ↦ norm_nonneg _
  rw [abs_of_nonneg hn]
  have hcomp : IsCompact (Iic T) := by rw [← Icc_bot]; exact isCompact_Icc
  have hbX : BddAbove (range (fun t : Iic T ↦ ‖X t.val ω‖)) := by
    simpa only [image_eq_range] using hcomp.bddAbove_image hx.norm
  have hbY : BddAbove (range (fun t : Iic T ↦ ‖Y t.val ω‖)) := by
    simpa only [image_eq_range] using hcomp.bddAbove_image hy.norm
  apply ciSup_le
  intro t
  exact (norm_add_le _ _).trans (add_le_add (le_ciSup hbX t) (le_ciSup hbY t))

omit [IsProbabilityMeasure μ] in
/-- A square-integrable random constant has precisely its random norm as
whole-path supremum, including the zero-length horizon. -/
theorem constant_S2 {E : Type*} [NormedAddCommGroup E] (T : ℝ≥0) {ξ : Ω → E} (hξ : MemLp ξ 2 μ) :
    MemLp (pathSup (fun _ ↦ ξ) T) 2 μ := by
  letI : Nonempty (Iic T) := ⟨⟨T,show T ≤ T from le_rfl⟩⟩
  change MemLp (fun ω ↦ ⨆ _ : Iic T, ‖ξ ω‖) 2 μ
  simpa only [ciSup_const] using hξ.norm

omit [IsProbabilityMeasure μ] in
/-- Finite sums retain genuine whole-path S² integrability. -/
theorem pathSup_sum_memLp {E : Type*} [NormedAddCommGroup E] {ι : Type*} (s : Finset ι) (T : ℝ≥0)
    (X : ι → ℝ≥0 → Ω → E)
    (ha : ∀ i ∈ s, StronglyAdapted 𝓕 (X i))
    (hc : ∀ i ∈ s, ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X i t ω) (Iic T))
    (h2 : ∀ i ∈ s, MemLp (pathSup (X i) T) 2 μ) :
    MemLp (pathSup (fun t ω ↦ ∑ i ∈ s, X i t ω) T) 2 μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change MemLp (pathSup (fun _ : ℝ≥0 ↦ (0 : Ω → E)) T) 2 μ
    exact constant_S2 T (MemLp.zero : MemLp (0 : Ω → E) 2 μ)
  | @insert i s his ih =>
    simp only [Finset.sum_insert his]
    apply pathSup_add_memLp T (ha i (Finset.mem_insert_self _ _))
    · intro t
      convert (Finset.stronglyMeasurable_sum s fun j hj ↦ ha j (Finset.mem_insert_of_mem hj) t) using 1
      funext ω
      exact (Finset.sum_apply ω s (fun j ↦ X j t)).symm
    · exact hc i (Finset.mem_insert_self _ _)
    · have hall : ∀ᵐ ω ∂μ, ∀ j ∈ s, ContinuousOn (fun t ↦ X j t ω) (Iic T) := by
        exact (ae_ball_iff s.countable_toSet).mpr (fun j hj ↦ hc j (Finset.mem_insert_of_mem hj))
      filter_upwards [hall] with ω hω
      exact continuousOn_finsetSum s hω
    · exact h2 i (Finset.mem_insert_self _ _)
    · exact ih (fun j hj ↦ ha j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ hc j (Finset.mem_insert_of_mem hj))
        (fun j hj ↦ h2 j (Finset.mem_insert_of_mem hj))

section Ito
variable {ι : Type*} [Fintype ι] {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  [𝓕.IsComplete μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t ↦ W i t ω)

include hW hWc

omit [Fintype ι] in
/-- The specific predictable Itô representative used in Picard has S²
integrability; this follows by indistinguishability from the constructed
continuous martingale version, rather than an assumed estimate for limUnder. -/
theorem itoContinuousMod_S2 (i : ι) (T : ℝ≥0) (g : H2 𝓕 μ T) :
    MemLp (pathSup (CommonItoContinuous.itoContinuousMod T (hWm i) g) T) 2 μ := by
  obtain ⟨Y,he,hc,hm,hy2,hbound,hint⟩ :=
    CommonFiltrationCompletion.exists_s2_on_complete_filtration (hW i) T (hWm i) (hWc i) g
  have hxc := CommonItoContinuous.itoContinuousMod_continuousOn (hW i) T (hWm i) (hWc i) g
  have hset : Icc (0 : ℝ≥0) T = Iic T := by ext t; simp
  rw [hset] at hxc
  have heq := indistinguishable_on_Iic T _ Y hxc (ae_of_all _ fun ω ↦ (hc ω).continuousOn)
    (fun t ht ↦ (CommonItoContinuous.itoContinuousMod_modification
      (hW i) T (hWm i) (hWc i) g ht).trans (he t ht).symm)
  exact (memLp_congr_ae (pathSup_congr T heq)).mpr hy2

/-- The actual predictable state representative, including its initial,
deterministic drift and every channel integral, belongs to S². -/
theorem realization_S2 (i₀ : ι) (T : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[𝓕 0] ξ) (hξ2 : MemLp ξ 2 μ)
    (g : H2 𝓕 μ T) (σ : ι → H2 𝓕 μ T) :
    MemLp (pathSup (realization hWm i₀ T ξ g σ) T) 2 μ := by
  have hset : Icc (0 : ℝ≥0) T = Iic T := by ext t; simp
  have hda : StronglyAdapted 𝓕 (CommonDriftPredictable.driftContinuousMod T (hWm i₀) g) :=
    (CommonDriftPredictable.driftContinuousMod_isStronglyPredictable T (hWm i₀) g).isStronglyProgressive.stronglyAdapted
  have hdc := CommonDriftPathwise.driftContinuousMod_continuousOn T (hWm i₀) g
  rw [hset] at hdc
  have hia (i : ι) : StronglyAdapted 𝓕 (CommonItoContinuous.itoContinuousMod T (hWm i) (σ i)) :=
    (CommonItoPredictable.itoContinuousMod_isStronglyPredictable (hW i) T (hWm i) (hWc i) (σ i)).isStronglyProgressive.stronglyAdapted
  have hic (i : ι) : ∀ᵐ ω ∂μ, ContinuousOn
      (fun t ↦ CommonItoContinuous.itoContinuousMod T (hWm i) (σ i) t ω) (Iic T) := by
    simpa only [hset] using CommonItoContinuous.itoContinuousMod_continuousOn (hW i) T (hWm i) (hWc i) (σ i)
  have hsuma : StronglyAdapted 𝓕 (fun t ω ↦ ∑ i, CommonItoContinuous.itoContinuousMod T (hWm i) (σ i) t ω) := by
    intro t
    convert (Finset.stronglyMeasurable_sum Finset.univ fun i _ ↦ hia i t) using 1
    funext ω
    exact (Finset.sum_apply ω Finset.univ (fun i ↦ CommonItoContinuous.itoContinuousMod T (hWm i) (σ i) t)).symm
  have hsumc : ∀ᵐ ω ∂μ, ContinuousOn
      (fun t ↦ ∑ i, CommonItoContinuous.itoContinuousMod T (hWm i) (σ i) t ω) (Iic T) := by
    have hall : ∀ᵐ ω ∂μ, ∀ i, ContinuousOn
        (fun t ↦ CommonItoContinuous.itoContinuousMod T (hWm i) (σ i) t ω) (Iic T) := by
      rw [ae_all_iff]; exact hic
    filter_upwards [hall] with ω hω
    exact continuousOn_finsetSum _ fun i _ ↦ hω i
  have hξa : StronglyAdapted 𝓕 (fun _ ↦ ξ) := fun t ↦ hξ.mono (𝓕.mono (show (0:ℝ≥0) ≤ t from zero_le))
  have hξc : ∀ᵐ ω ∂μ, ContinuousOn (fun _ : ℝ≥0 ↦ ξ ω) (Iic T) := ae_of_all _ fun _ ↦ continuousOn_const
  have hfirst := pathSup_add_memLp T hξa hda hξc hdc (constant_S2 T hξ2)
    (driftContinuousMod_S2 T (hWm i₀) g)
  have hfirsta : StronglyAdapted 𝓕 (fun t ω ↦ ξ ω + CommonDriftPredictable.driftContinuousMod T (hWm i₀) g t ω) :=
    fun t ↦ (hξa t).add (hda t)
  have hfirstc : ∀ᵐ ω ∂μ, ContinuousOn
      (fun t ↦ ξ ω + CommonDriftPredictable.driftContinuousMod T (hWm i₀) g t ω) (Iic T) :=
    hdc.mono fun _ h ↦ continuousOn_const.add h
  exact pathSup_add_memLp T hfirsta hsuma hfirstc hsumc hfirst
    (pathSup_sum_memLp Finset.univ T _ (fun i _ ↦ hia i) (fun i _ ↦ hic i)
      (fun i _ ↦ itoContinuousMod_S2 hW hWm hWc i T (σ i)))

end Ito
omit [IsProbabilityMeasure μ] in
/-- A finite orthonormal reconstruction has square-integrable Euclidean
whole-path norm whenever its genuine scalar coordinates belong to S². -/
theorem vector_reconstruct_S2 {E κ : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype κ] (b : OrthonormalBasis κ ℝ E)
    (T : ℝ≥0) (X : κ → ℝ≥0 → Ω → ℝ)
    (ha : ∀ a, StronglyAdapted 𝓕 (X a))
    (hc : ∀ a, ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ X a t ω) (Iic T))
    (h2 : ∀ a, MemLp (pathSup (X a) T) 2 μ) :
    MemLp (pathSup (fun t ω ↦ ∑ a, X a t ω • b a) T) 2 μ := by
  apply pathSup_sum_memLp Finset.univ T
  · intro a _ t
    exact (ha a t).smul_const (b a)
  · intro a _
    filter_upwards [hc a] with ω hω
    exact hω.smul continuousOn_const
  · intro a _
    have he : pathSup (fun t ω ↦ X a t ω • b a) T = pathSup (X a) T := by
      funext ω
      unfold pathSup
      simp only [norm_smul,b.norm_eq_one,mul_one]
    rw [he]
    exact h2 a

/-- Full finite-dimensional state S² integrability in the actual Hilbert norm,
for the matrix-driven pathwise representative constructed by Picard. -/
theorem state_reconstruction_S2 {E κ ν ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype κ] [Fintype ν] [Fintype ι]
    (b : OrthonormalBasis κ ℝ E) {W : ι → ℝ≥0 → Ω → ℝ}
    [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ] [𝓕.IsComplete μ]
    (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
    (hWc : ∀ i ω, Continuous fun t ↦ W i t ω) (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ a, StronglyMeasurable[𝓕 0] (ξ a))
    (hξ2 : ∀ a, MemLp (ξ a) 2 μ) (u : ν → H2 𝓕 μ T) (X : κ → H2 𝓕 μ T) :
    MemLp (pathSup (fun t ω ↦ ∑ a,
      CommonLocalSolution.stateProcess hWm i₀ T A B C D ξ u X a t ω • b a) T) 2 μ := by
  apply vector_reconstruct_S2 b T
  · intro a
    exact (realization_predictable hW hWm hWc i₀ T (hξ a) _ _).isStronglyProgressive.stronglyAdapted
  · intro a
    have hset : Icc (0 : ℝ≥0) T = Iic T := by ext t; simp
    simpa only [hset,CommonLocalSolution.stateProcess] using realization_continuousOn hW hWm hWc i₀ T (ξ a)
      (CommonLocalSolution.driftInput T A B u X a) (fun i ↦ CommonLocalSolution.noiseInput T C D u X i a)
  · intro a
    exact realization_S2 hW hWm hWc i₀ T (hξ a) (hξ2 a) _ _

end LinearStochastic.CommonStateS2
