import LinearStochastic.InitialExpectedProduct
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The actual finite-channel Itô terminal map as an isometric embedding.
Its adjoint extracts representation coefficients; representation existence is
not asserted here. All independence assumptions concern the Brownian drivers. -/
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace LinearStochastic.BSDEIntegralRange
open MeasureTheory ProbabilityTheory Set
open scoped NNReal InnerProductSpace BigOperators
open CommonItoMultichannel ItoExpectedProduct
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ι : Type*} [Fintype ι] {W : ι → ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hpair : ∀ i j, CommonItoCross.PairForwardIndependent (W i) (W j) 𝓕 μ)
  (hchannels : ∀ i j, i ≠ j → IndepFun (fun ω t ↦ W i t ω) (fun ω t ↦ W j t ω) μ)

/-- The true Hilbert direct sum of the channel integrand spaces. -/
abbrev ChannelH2 (T : ℝ≥0) := PiLp 2 (fun _ : ι ↦ Lp ℝ 2 (spacetimeMeasure 𝓕 μ T))

instance channelComplete (T : ℝ≥0) : CompleteSpace (ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) := by
  exact @PiLp.completeSpace 2 ι (fun _ : ι ↦ Lp ℝ 2 (spacetimeMeasure 𝓕 μ T))
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance)

/-- Actual constructed Itô integral, with the correct channel Hilbert norm. -/
def integral (T : ℝ≥0) : ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T →ₗᵢ[ℝ] Lp ℝ 2 μ where
  toFun f := sumIntegral hW hWm T (fun i ↦ f i)
  map_add' f g := by
    simp only [sumIntegral,PiLp.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [sumIntegral,PiLp.smul_apply,map_smul,Finset.smul_sum,RingHom.id_apply]
  norm_map' f := by
    change ‖sumIntegral hW hWm T (fun i ↦ f i)‖ = ‖f‖
    have h := sumIntegral_norm_sq hW hWm hpair hchannels T (fun i ↦ f i)
    rw [← PiLp.norm_sq_eq_of_L2] at h
    nlinarith [norm_nonneg f,norm_nonneg (sumIntegral hW hWm T (fun i ↦ f i))]

theorem integral_apply (T : ℝ≥0) (f : ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    integral hW hWm hpair hchannels T f = sumIntegral hW hWm T (fun i ↦ f i) := rfl

/-- Completeness of genuine predictable L² yields closed actual integral range. -/
theorem integral_range_isClosed (T : ℝ≥0) :
    IsClosed (Set.range (integral hW hWm hpair hchannels T)) :=
  (integral hW hWm hpair hchannels T).isometry.isClosedEmbedding.isClosed_range

/-- Every constructed terminal integral belongs to the original terminal sigma algebra. -/
theorem integral_terminal_measurable (T : ℝ≥0) (f : ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    AEStronglyMeasurable[𝓕 T] (integral hW hWm hpair hchannels T f) μ :=
  ((sumProcess_martingale hW hWm T (fun i ↦ f i)).1 T).aestronglyMeasurable.congr
    (sumProcess_terminal_ae hW hWm T (fun i ↦ f i))

/-- Initial random variables are orthogonal to the actual Itô terminal range. -/
theorem initial_integral_orthogonal (T : ℝ≥0) (ξ : Lp ℝ 2 μ)
    (hξ : AEStronglyMeasurable[𝓕 0] ξ μ)
    (f : ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    inner ℝ ξ (integral hW hWm hpair hchannels T f) = 0 := by
  have hz := InitialExpectedProduct.initial_martingale_pairing_zero (ξ : Ω → ℝ)
    (Lp.memLp ξ) hξ (sumProcess hW hWm T (fun i ↦ f i))
    (sumProcess_martingale hW hWm T (fun i ↦ f i)) T
    (sumProcess_memLp hW hWm T T (fun i ↦ f i))
    (InitialExpectedProduct.sumProcess_zero_ae hW hWm T (fun i ↦ f i))
  rw [L2.inner_def]
  refine (integral_congr_ae ?_).trans hz
  filter_upwards [sumProcess_terminal_ae hW hWm T (fun i ↦ f i)] with ω hω
  rw [hω]
  rfl

/-- Exact energy of an initial variable plus actual terminal Itô integral. -/
theorem decomposition_energy (T : ℝ≥0) (ξ : Lp ℝ 2 μ)
    (hξ : AEStronglyMeasurable[𝓕 0] ξ μ)
    (f : ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    ‖ξ + integral hW hWm hpair hchannels T f‖^2 = ‖ξ‖^2 + ‖f‖^2 := by
  rw [norm_add_sq_real,initial_integral_orthogonal hW hWm hpair hchannels T ξ hξ f,
    (integral hW hWm hpair hchannels T).norm_map]
  ring

/-- True representation coefficients are unique, including their initial term. -/
theorem decomposition_unique (T : ℝ≥0) (ξ η : Lp ℝ 2 μ)
    (hξ : AEStronglyMeasurable[𝓕 0] ξ μ) (hη : AEStronglyMeasurable[𝓕 0] η μ)
    (f g : ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T)
    (he : ξ + integral hW hWm hpair hchannels T f = η + integral hW hWm hpair hchannels T g) :
    ξ = η ∧ f = g := by
  have hzero : ξ - η + integral hW hWm hpair hchannels T (f-g) = 0 := by
    rw [map_sub]
    calc
      _ = (ξ + integral hW hWm hpair hchannels T f) - (η + integral hW hWm hpair hchannels T g) := by abel
      _ = 0 := sub_eq_zero.mpr he
  have henergy := decomposition_energy hW hWm hpair hchannels T (ξ-η) ((hξ.sub hη).congr (Lp.coeFn_sub ξ η).symm) (f-g)
  rw [hzero,norm_zero,zero_pow (by decide : 2 ≠ 0)] at henergy
  have hx : ‖ξ-η‖ = 0 := by nlinarith [sq_nonneg ‖f-g‖,norm_nonneg (ξ-η)]
  have hf : ‖f-g‖ = 0 := by nlinarith [sq_nonneg ‖ξ-η‖,norm_nonneg (f-g)]
  exact ⟨sub_eq_zero.mp (norm_eq_zero.mp hx),sub_eq_zero.mp (norm_eq_zero.mp hf)⟩

/-- The adjoint of the actual isometric Itô embedding is a bounded coefficient
extractor. No representation-existence theorem is presumed by this definition. -/
def coefficients (T : ℝ≥0) : Lp ℝ 2 μ →L[ℝ] ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T :=
  (integral hW hWm hpair hchannels T).toContinuousLinearMap.adjoint

/-- The extractor recovers every actual integrand from its terminal integral. -/
theorem coefficients_integral (T : ℝ≥0) (f : ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    coefficients hW hWm hpair hchannels T (integral hW hWm hpair hchannels T f) = f := by
  apply ext_inner_right ℝ
  intro g
  change inner ℝ ((integral hW hWm hpair hchannels T).toContinuousLinearMap.adjoint
    (integral hW hWm hpair hchannels T f)) g = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (integral hW hWm hpair hchannels T).inner_map_map f g

/-- Initial F₀ variables have zero extracted diffusion coefficient. -/
theorem coefficients_initial (T : ℝ≥0) (ξ : Lp ℝ 2 μ)
    (hξ : AEStronglyMeasurable[𝓕 0] ξ μ) :
    coefficients hW hWm hpair hchannels T ξ = 0 := by
  apply ext_inner_right ℝ
  intro f
  change inner ℝ ((integral hW hWm hpair hchannels T).toContinuousLinearMap.adjoint ξ) f = _
  rw [ContinuousLinearMap.adjoint_inner_left,inner_zero_left]
  exact initial_integral_orthogonal hW hWm hpair hchannels T ξ hξ f

/-- Extraction is a contraction on the actual terminal L² space. -/
theorem coefficients_norm (T : ℝ≥0) (χ : Lp ℝ 2 μ) :
    ‖coefficients hW hWm hpair hchannels T χ‖ ≤ ‖χ‖ := by
  have hnorm : ‖coefficients hW hWm hpair hchannels T‖ ≤ 1 := by
    rw [coefficients,ContinuousLinearMap.adjoint.norm_map]
    exact (integral hW hWm hpair hchannels T).norm_toContinuousLinearMap_le
  exact ((coefficients hW hWm hpair hchannels T).le_opNorm χ).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hnorm (norm_nonneg χ))

/-- If an actual decomposition exists, its integrand is the canonical bounded
extractor. This implication asserts neither existence nor density. -/
theorem coefficients_of_decomposition (T : ℝ≥0) (χ ξ : Lp ℝ 2 μ)
    (hξ : AEStronglyMeasurable[𝓕 0] ξ μ)
    (f : ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T)
    (he : χ = ξ + integral hW hWm hpair hchannels T f) :
    coefficients hW hWm hpair hchannels T χ = f := by
  rw [he,map_add,coefficients_initial hW hWm hpair hchannels T ξ hξ,
    coefficients_integral,zero_add]

/-- Actual conditional expectation at the initial sigma algebra. -/
def initialProjection (χ : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  condExpL2 ℝ ℝ (𝓕.le 0) χ

omit [IsProbabilityMeasure μ] in
/-- The initial projection fixes every measurable L² initial value. -/
theorem initialProjection_of_measurable (ξ : Lp ℝ 2 μ)
    (hξ : AEStronglyMeasurable[𝓕 0] ξ μ) : initialProjection (𝓕:=𝓕) ξ = ξ := by
  apply ext_inner_left ℝ
  intro η
  change inner ℝ η (condExpL2 ℝ ℝ (𝓕.le 0) ξ : Lp ℝ 2 μ) = _
  rw [← inner_condExpL2_left_eq_right,inner_condExpL2_eq_inner_fun (𝓕.le 0) η ξ hξ]

/-- An actual constructed Itô terminal integral has conditional expectation
zero given F₀; this is derived from its genuine martingale, not assumed. -/
theorem initialProjection_integral (T : ℝ≥0) (f : ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T) :
    initialProjection (𝓕:=𝓕) (integral hW hWm hpair hchannels T f) = 0 := by
  apply (inner_self_eq_zero (𝕜:=ℝ)).mp
  let I := integral hW hWm hpair hchannels T f
  change inner ℝ (condExpL2 ℝ ℝ (𝓕.le 0) I : Lp ℝ 2 μ)
    (condExpL2 ℝ ℝ (𝓕.le 0) I : Lp ℝ 2 μ) = 0
  rw [inner_condExpL2_eq_inner_fun (𝓕.le 0) _ _ (aestronglyMeasurable_condExpL2 (𝓕.le 0) _),
    real_inner_comm]
  exact initial_integral_orthogonal hW hWm hpair hchannels T _
    (aestronglyMeasurable_condExpL2 (𝓕.le 0) _) f

/-- A represented terminal variable's initial value is its actual conditional
expectation, with no trivial-F₀ assumption. -/
theorem initial_of_decomposition (T : ℝ≥0) (χ ξ : Lp ℝ 2 μ)
    (hξ : AEStronglyMeasurable[𝓕 0] ξ μ)
    (f : ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T)
    (he : χ = ξ + integral hW hWm hpair hchannels T f) :
    initialProjection (𝓕:=𝓕) χ = ξ := by
  rw [he]
  change (condExpL2 ℝ ℝ (𝓕.le 0) (ξ + _) : Lp ℝ 2 μ) = ξ
  rw [map_add,Submodule.coe_add]
  change initialProjection (𝓕:=𝓕) ξ + initialProjection (𝓕:=𝓕) _ = ξ
  rw [initialProjection_of_measurable ξ hξ,initialProjection_integral,add_zero]

/-- True terminal energy controls the represented diffusion in the Hilbert
channel norm; no coordinate maximum replaces the sum-of-squares norm. -/
theorem decomposition_bound (T : ℝ≥0) (χ ξ : Lp ℝ 2 μ)
    (hξ : AEStronglyMeasurable[𝓕 0] ξ μ)
    (f : ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T)
    (he : χ = ξ + integral hW hWm hpair hchannels T f) : ‖f‖ ≤ ‖χ‖ := by
  rw [← coefficients_of_decomposition hW hWm hpair hchannels T χ ξ hξ f he]
  exact coefficients_norm hW hWm hpair hchannels T χ

/-- Terminal variables admitting an actual initial-plus-Itô decomposition. -/
def Represented (T : ℝ≥0) (χ : Lp ℝ 2 μ) : Prop :=
  ∃ ξ : Lp ℝ 2 μ, AEStronglyMeasurable[𝓕 0] ξ μ ∧
    ∃ f : ChannelH2 (ι:=ι) (𝓕:=𝓕) (μ:=μ) T,
      χ = ξ + integral hW hWm hpair hchannels T f

/-- Representability is exactly the fixed-point identity for the actual
conditional expectation and actual Itô embedding/adjoint. -/
theorem represented_iff (T : ℝ≥0) (χ : Lp ℝ 2 μ) :
    Represented hW hWm hpair hchannels T χ ↔
      χ = initialProjection (𝓕:=𝓕) χ + integral hW hWm hpair hchannels T
        (coefficients hW hWm hpair hchannels T χ) := by
  constructor
  · rintro ⟨ξ,hξ,f,he⟩
    rw [initial_of_decomposition hW hWm hpair hchannels T χ ξ hξ f he,
      coefficients_of_decomposition hW hWm hpair hchannels T χ ξ hξ f he]
    exact he
  · intro he
    exact ⟨initialProjection (𝓕:=𝓕) χ,aestronglyMeasurable_condExpL2 (𝓕.le 0) χ,
      coefficients hW hWm hpair hchannels T χ,he⟩

/-- The whole initial-plus-integral representable set is closed; this includes
nontrivial F₀ and is the precise closedness needed for a density proof. -/
theorem represented_isClosed (T : ℝ≥0) :
    IsClosed {χ : Lp ℝ 2 μ | Represented hW hWm hpair hchannels T χ} := by
  have he : {χ : Lp ℝ 2 μ | Represented hW hWm hpair hchannels T χ} =
      {χ | χ = initialProjection (𝓕:=𝓕) χ + integral hW hWm hpair hchannels T
        (coefficients hW hWm hpair hchannels T χ)} := by
    ext χ
    exact represented_iff hW hWm hpair hchannels T χ
  rw [he]
  apply isClosed_eq continuous_id
  exact (continuous_subtype_val.comp (condExpL2 ℝ ℝ (𝓕.le 0)).continuous).add
    ((integral hW hWm hpair hchannels T).continuous.comp
      (coefficients hW hWm hpair hchannels T).continuous)

end LinearStochastic.BSDEIntegralRange
