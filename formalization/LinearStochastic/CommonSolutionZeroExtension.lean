import LinearStochastic.VectorH2Extension
import LinearStochastic.CommonSolutionPaste

/-! Actual zero-initial SDE solutions can be placed after a zero time segment.
The predictable state and input are the real isometric window extensions, and
all path and stochastic integral identities are proved. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace LinearStochastic.CommonSolutionZeroExtension
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open CommonItoMultichannel CommonVectorPicard CommonLocalSolution CommonSolutionData
open CommonHorizonRestriction CommonShiftH2 CommonShiftSimple CommonIntegralPaste CommonItoCLM
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))

/-- The actual integral equation with zero initial value, drift and diffusion
has the literal zero path. -/
theorem zero_equation (T : ℝ≥0) :
    IntegralEquation (𝓕:=𝓕) hW hWm T 0 0 (fun _ ↦ 0) 0 := by
  have ha : ((0 : H2 𝓕 μ T) : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T T).prod μ] (fun _ ↦ 0) :=
    ae_of_ae_trim 𝓕.predictable_le_prod (Lp.coeFn_zero ℝ 2 (spacetimeMeasure 𝓕 μ T))
  have hp := CommonLocalCoefficients.primitive_congr_spacetime T (f:=fun t ω ↦ (0 : H2 𝓕 μ T) (t,ω)) (g:=0) ha
  intro t ht
  have hi : ∀ᵐ ω ∂μ, ∀ i : ι,
      CommonItoProcessGeneral.itoProcessCLM (hW i) T t (hWm i) (0 : H2 𝓕 μ T) ω = 0 := by
    rw [ae_all_iff]
    intro i
    rw [map_zero]
    exact Lp.coeFn_zero ℝ 2 μ
  filter_upwards [hp,hi] with ω hp hi
  have hd := hp t ht
  simp only [Pi.zero_apply,integral_zero] at hd
  simp only [Pi.zero_apply,hd,hi,zero_add,Finset.sum_const_zero]

local instance shiftedForwardFamily (a : ℝ≥0) :
    ∀ i, CommonItoIsometry.ForwardIndependent (CommonTimeShift.driver (W i) a) (CommonTimeShift.filtration 𝓕 a) μ :=
  fun _ ↦ CommonTimeShift.forwardIndependent a

/-- A genuine local zero-initial solution is translated onto [a,a+δ], retaining
its actual H² state as the exact zero extension and its terminal path. -/
def extend (i₀ : ι) (a δ : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (u : ν → H2 (CommonTimeShift.filtration 𝓕 a) μ δ)
    (q : Solution (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a) δ A B C D 0 u) :
    Solution hW hWm (a+δ) A B C D 0
      (fun j ↦ CommonH2Extension.extendShift (𝓕:=𝓕) (μ:=μ) (hWm i₀) a δ (a+δ) le_rfl (u j)) := by
  let ext := CommonH2Extension.extendShift (𝓕:=𝓕) (μ:=μ) (hWm i₀) a δ (a+δ) le_rfl
  let X := fun j ↦ ext (q.X j)
  let v := fun j ↦ ext (u j)
  let R := fun j ↦ CommonProcessPaste.paste a (0 : ℝ≥0 → Ω → ℝ) (q.path j)
  have hzero : IsProgressive 𝓕 (0 : ℝ≥0 → Ω → ℝ) := by
    apply IsStronglyProgressive.isProgressive
    intro t
    exact stronglyMeasurable_zero
  have hzcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t ↦ (0 : ℝ≥0 → Ω → ℝ) t ω) (Iic a) :=
    Filter.Eventually.of_forall (fun _ ↦ continuousOn_const)
  have hz2 : MemLp (ContinuousDoobL2.pathSup (0 : ℝ≥0 → Ω → ℝ) a) 2 μ := by
    have he : ContinuousDoobL2.pathSup (0 : ℝ≥0 → Ω → ℝ) a = (0 : Ω → ℝ) := by
      funext ω
      simp [ContinuousDoobL2.pathSup]
    rw [he]
    exact MemLp.zero
  have hrep (j : κ) : (X j : ℝ≥0 × Ω → ℝ) =ᵐ[(timeMeasure_T (a+δ)).prod μ] Function.uncurry (R j) := by
    have hw := VectorH2Extension.window_ae (μ:=μ) a δ (a+δ) le_rfl
      (fun z ↦ q.X j z = q.path j z.1 z.2) (q.representative j)
    have htime : ∀ᵐ t ∂timeMeasure_T (a+δ), t ≤ a+δ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t htm using htm.2
    have ht : ∀ᵐ z ∂(timeMeasure_T (a+δ)).prod μ, z.1 ≤ a+δ :=
      Measure.quasiMeasurePreserving_fst.ae htime
    filter_upwards [CommonH2Extension.extendShift_ae (hWm i₀) a δ (a+δ) le_rfl (q.X j),hw,ht]
      with z he hw ht
    change ext (q.X j) z = CommonProcessPaste.paste a 0 (q.path j) z.1 z.2
    rw [show ext (q.X j) z = _ from he]
    unfold CommonProcessPaste.paste
    by_cases hh : z.1 ≤ a
    · simp [hh,not_lt_of_ge hh]
    · have hw' : a < z.1 ∧ z.1 ≤ a+δ := ⟨lt_of_not_ge hh,ht⟩
      rw [if_pos hw',if_neg hh]
      exact hw hw' 
  have hpre (M : Matrix κ κ ℝ) (N : Matrix κ ν ℝ) (j : κ) :
      restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl) (driftInput (a+δ) M N v X j) = 0 := by
    simp only [driftInput,Pi.add_apply,matrixAction_apply]
    simp only [map_add,map_sum,map_smul]
    have hx (k : κ) : restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl) (X k) = 0 :=
      CommonH2Extension.restriction_extendShift_zero (hWm i₀) a δ (a+δ) a le_rfl le_rfl (q.X k)
    have hu (l : ν) : restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl) (v l) = 0 :=
      CommonH2Extension.restriction_extendShift_zero (hWm i₀) a δ (a+δ) a le_rfl le_rfl (u l)
    simp only [hx,hu,smul_zero,Finset.sum_const_zero,add_zero]
  have hshift (M : Matrix κ κ ℝ) (N : Matrix κ ν ℝ) (j : κ) :
      shiftCLM a δ (a+δ) le_rfl (driftInput (a+δ) M N v X j) = driftInput δ M N u q.X j := by
    simp only [driftInput,Pi.add_apply,matrixAction_apply]
    simp only [map_add,map_sum,map_smul]
    have hx (k : κ) : shiftCLM a δ (a+δ) le_rfl (X k) = q.X k :=
      CommonH2Extension.shift_extendShift (hWm i₀) a δ (a+δ) le_rfl (q.X k)
    have hu (l : ν) : shiftCLM a δ (a+δ) le_rfl (v l) = u l :=
      CommonH2Extension.shift_extendShift (hWm i₀) a δ (a+δ) le_rfl (u l)
    simp only [hx,hu]
  refine ⟨X,R,fun j ↦ CommonProcessPaste.progressive a hzero (q.progressive j),?_,?_,hrep,?_,?_⟩
  · intro j
    filter_upwards [q.continuous j,q.initial j] with ω hc hi
    exact CommonProcessPaste.continuousOn a δ _ _ continuousOn_const hc hi.symm
  · intro j
    exact CommonProcessPaste.paste_S2 μ a δ hzero (q.progressive j) hzcont (q.continuous j)
      (q.initial j).symm hz2 (q.squareSup j)
  · intro j
    change CommonProcessPaste.paste a 0 (q.path j) 0 =ᵐ[μ] 0
    rw [CommonProcessPaste.paste_zero]
    exact Filter.EventuallyEq.rfl
  · intro j
    apply CommonIntegralPaste.paste_equation hW hWm i₀ a δ 0
      (driftInput (a+δ) A B v X j) (fun i ↦ noiseInput (a+δ) C D v X i j) 0 (q.path j)
    · have hn (i : ι) : restriction (hWm i₀) (show a ≤ a+δ from le_add_right le_rfl)
          (noiseInput (a+δ) C D v X i j) = 0 := hpre (C i) (D i) j
      have he := zero_equation (𝓕:=𝓕) hW hWm a
      convert he using 1
      · exact hpre A B j
      · exact funext hn
    · have hn (i : ι) : shiftCLM a δ (a+δ) le_rfl (noiseInput (a+δ) C D v X i j) =
          noiseInput δ C D u q.X i j := hshift (C i) (D i) j
      simpa only [Pi.zero_apply,hshift,hn] using q.equation j

/-- Coordinate state norms are preserved exactly by the actual extension. -/
theorem extend_state_norm (i₀ : ι) (a δ : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (u : ν → H2 (CommonTimeShift.filtration 𝓕 a) μ δ)
    (q : Solution (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i ↦ CommonTimeShift.preBrownian (hW i) a) (fun i ↦ shiftedMeas (hWm i) a) δ A B C D 0 u) :
    ‖(extend hW hWm i₀ a δ A B C D u q).X‖ = ‖q.X‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    change ‖CommonH2Extension.extendShift (𝓕:=𝓕) (μ:=μ) (hWm i₀) a δ (a+δ) le_rfl (q.X j)‖ ≤ _
    rw [(CommonH2Extension.extendShift (𝓕:=𝓕) (μ:=μ) (hWm i₀) a δ (a+δ) le_rfl).norm_map]
    exact norm_le_pi_norm q.X j
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    have hh := norm_le_pi_norm (extend hW hWm i₀ a δ A B C D u q).X j
    simpa only [extend,(CommonH2Extension.extendShift (𝓕:=𝓕) (μ:=μ) (hWm i₀) a δ (a+δ) le_rfl).norm_map] using hh
end LinearStochastic.CommonSolutionZeroExtension
