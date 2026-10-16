import LinearStochastic.CommonItoCLM
import LinearStochastic.ExpectedProduct

/-!
# Actual real-time transport for the common-filtration stochastic integral

The NNReal clock carries the comap of Lebesgue measure. The following results
identify its finite horizon with the manuscript's real interval, transport raw
spacetime L² functions, and pull genuine martingales back along max(t,0).
-/
noncomputable section
namespace LinearStochastic.RealTimeBridge
open MeasureTheory Set
open scoped NNReal

/-- The actual finite-horizon time measure agrees under the ordinary inclusion
with Lebesgue measure on the manuscript interval (0,T]. -/
theorem coe_measurePreserving (T : ℝ≥0) :
    MeasurePreserving ((↑) : ℝ≥0 → ℝ) (CommonItoCLM.timeMeasure_T T)
      (volume.restrict (Ioc 0 (T : ℝ))) := by
  refine ⟨NNReal.continuous_coe.measurable, ?_⟩
  have hf := CommonItoL2.measurableEmbedding_nnrealCoe
  have himg : ((↑) : ℝ≥0 → ℝ) '' Ioc 0 T = Ioc 0 (T : ℝ) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨by exact_mod_cast hy.1, by exact_mod_cast hy.2⟩
    · intro hx
      exact ⟨⟨x,hx.1.le⟩,⟨by exact_mod_cast hx.1,by exact_mod_cast hx.2⟩,rfl⟩
  rw [CommonItoCLM.timeMeasure_T, CommonItoL2.timeMeasure,
    hf.restrict_comap, hf.map_comap,
    Measure.restrict_restrict hf.measurableSet_range,
    inter_eq_right.mpr (image_subset_range _ _), himg]

/-- The inverse clock map is measure-preserving on the actual restricted
real interval; its collapse of negative time is outside this measure. -/
theorem toNNReal_measurePreserving (T : ℝ≥0) :
    MeasurePreserving Real.toNNReal (volume.restrict (Ioc 0 (T : ℝ)))
      (CommonItoCLM.timeMeasure_T T) := by
  refine ⟨measurable_real_toNNReal, ?_⟩
  rw [← (coe_measurePreserving T).map_eq,
    Measure.map_map measurable_real_toNNReal NNReal.continuous_coe.measurable]
  simp only [Function.comp_def, Real.toNNReal_coe]
  exact Measure.map_id

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Spacetime H² is transported by the genuine clock map and the identity on
the sample space. This uses product-measure preservation, not a new norm axiom. -/
theorem memLp_real_extension (T : ℝ≥0) (P : Measure Ω) [SFinite P]
    (f : ℝ≥0 → Ω → E)
    (hf : MemLp (Function.uncurry f) 2 ((CommonItoCLM.timeMeasure_T T).prod P)) :
    MemLp (fun z : ℝ × Ω => f z.1.toNNReal z.2) 2
      ((volume.restrict (Ioc 0 (T : ℝ))).prod P) :=
  hf.comp_measurePreserving ((toNNReal_measurePreserving T).prod (MeasurePreserving.id P))

/-- Extension of a nonnegative-time filtration to real time by freezing the
past at time zero. On every nonnegative time it is exactly the given filtration. -/
def filtration (𝓕 : Filtration ℝ≥0 mΩ) : Filtration ℝ mΩ where
  seq t := 𝓕 t.toNNReal
  mono' _ _ h := 𝓕.mono (Real.toNNReal_mono h)
  le' t := 𝓕.le t.toNNReal

@[simp] theorem filtration_coe (𝓕 : Filtration ℝ≥0 mΩ) (t : ℝ≥0) :
    filtration 𝓕 (t : ℝ) = 𝓕 t := by simp [filtration]

/-- A genuine strong-adapted martingale remains a genuine martingale after
the monotone clock extension. No martingale property is inferred from L²
continuity or from an arbitrary representative. -/
theorem martingale_real_extension (P : Measure Ω) [CompleteSpace E]
    (𝓕 : Filtration ℝ≥0 mΩ) (M : ℝ≥0 → Ω → E) (hM : Martingale M 𝓕 P) :
    Martingale (fun t : ℝ => M t.toNNReal) (filtration 𝓕) P := by
  refine ⟨fun t => hM.1 t.toNNReal, ?_⟩
  intro s t hst
  exact hM.2 _ _ (Real.toNNReal_mono hst)

/-- Exact Bochner-integral transport for the real extension of any function.
The embedding theorem also handles the totalized integral convention correctly. -/
theorem integral_real_extension [CompleteSpace E] (T : ℝ≥0) (f : ℝ≥0 → E) :
    (∫ s in Ioc 0 (T : ℝ), f s.toNNReal) =
      ∫ s, f s ∂(CommonItoCLM.timeMeasure_T T) := by
  simpa only [Real.toNNReal_coe] using
    ((coe_measurePreserving T).integral_comp CommonItoL2.measurableEmbedding_nnrealCoe
      (fun s => f s.toNNReal)).symm

omit [NormedSpace ℝ E] in
/-- The actual predictable L² representative has the manuscript's spacetime
L² integrability after conversion to real time. -/
theorem predictable_memLp_real_extension (T : ℝ≥0) (P : Measure Ω) [SFinite P]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (f : Lp E 2 (((CommonItoCLM.timeMeasure_T T).prod P).trim 𝓕.predictable_le_prod)) :
    MemLp (fun z : ℝ × Ω => f (z.1.toNNReal,z.2)) 2
      ((volume.restrict (Ioc 0 (T : ℝ))).prod P) :=
  memLp_real_extension T P (Function.curry f)
    (memLp_of_memLp_trim 𝓕.predictable_le_prod (Lp.memLp f))

omit [NormedSpace ℝ E] in
/-- A predictable L² representative is actually strongly adapted at each
time, after the same clock extension. No a.e. version is silently substituted. -/
theorem predictable_real_stronglyAdapted (T : ℝ≥0) (P : Measure Ω)
    (𝓕 : Filtration ℝ≥0 mΩ)
    (f : Lp E 2 (((CommonItoCLM.timeMeasure_T T).prod P).trim 𝓕.predictable_le_prod)) :
    StronglyAdapted (filtration 𝓕) (fun t : ℝ => fun ω => f (t.toNNReal,ω)) := by
  have hp : IsStronglyPredictable 𝓕 (Function.curry f) := Lp.stronglyMeasurable f
  exact fun t => hp.stronglyAdapted t.toNNReal

/-- For a time before the horizon, the past part of the restricted real
measure is exactly the actual interval (0,s]. -/
theorem past_integral_real [CompleteSpace E] (T : ℝ≥0) (s : ℝ) (hs : s ≤ T)
    (f : ℝ → E) :
    (∫ t in Iic s, f t ∂(volume.restrict (Ioc 0 (T : ℝ)))) =
      ∫ t in Ioc 0 s, f t := by
  rw [Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioc_of_le hs]

end LinearStochastic.RealTimeBridge

namespace LinearStochastic.RealTimeBridge
open MeasureTheory Set
open scoped NNReal InnerProductSpace
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The genuine expected product in the manuscript's real time coordinate,
with arbitrary joint-predictable H² drifts and arbitrary genuine nonnegative-time
martingales. Both the drift integrals and their past values are actual Lebesgue
integrals on (0,T] and (0,s], not abstract terminal-map symbols. -/
theorem predictable_expected_product (T : ℝ≥0) (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (M N : ℝ≥0 → Ω → E)
    (hM : Martingale M 𝓕 P) (hN : Martingale N 𝓕 P)
    (hMT : MemLp (M T) 2 P) (hNT : MemLp (N T) 2 P)
    (f g : Lp E 2 (((CommonItoCLM.timeMeasure_T T).prod P).trim 𝓕.predictable_le_prod)) :
    (∫ ω, inner ℝ ((∫ s in Ioc 0 (T : ℝ), f (s.toNNReal,ω)) + M T ω)
      ((∫ s in Ioc 0 (T : ℝ), g (s.toNNReal,ω)) + N T ω) ∂P) =
      (∫ ω, inner ℝ (M T ω) (N T ω) ∂P) +
      (∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ (f (s.toNNReal,ω))
        ((∫ t in Ioc 0 s, g (t.toNNReal,ω)) + N s.toNNReal ω) ∂P) +
      (∫ s in Ioc 0 (T : ℝ), ∫ ω, inner ℝ
        ((∫ t in Ioc 0 s, f (t.toNNReal,ω)) + M s.toNNReal ω) (g (s.toNNReal,ω)) ∂P) := by
  let ν : Measure ℝ := volume.restrict (Ioc 0 (T : ℝ))
  have ht : ∀ᵐ s ∂ν, s ≤ (T : ℝ) :=
    (ae_restrict_mem measurableSet_Ioc).mono (fun _ hs => hs.2)
  have hf := predictable_memLp_real_extension T P 𝓕 f
  have hg := predictable_memLp_real_extension T P 𝓕 g
  have haf : ∀ᵐ s ∂ν, AEStronglyMeasurable[filtration 𝓕 s]
      (fun ω => f (s.toNNReal,ω)) P :=
    ae_of_all _ fun s => (predictable_real_stronglyAdapted T P 𝓕 f s).aestronglyMeasurable
  have hag : ∀ᵐ s ∂ν, AEStronglyMeasurable[filtration 𝓕 s]
      (fun ω => g (s.toNNReal,ω)) P :=
    ae_of_all _ fun s => (predictable_real_stronglyAdapted T P 𝓕 g s).aestronglyMeasurable
  have h := ExpectedProduct.expected_product ν P (filtration 𝓕)
    (fun s => M s.toNNReal) (fun s => N s.toNNReal)
    (martingale_real_extension P 𝓕 M hM) (martingale_real_extension P 𝓕 N hN)
    (fun s ω => f (s.toNNReal,ω)) (fun s ω => g (s.toNNReal,ω)) hf hg haf hag
    (T : ℝ) (by simpa only [Real.toNNReal_coe] using hMT)
    (by simpa only [Real.toNNReal_coe] using hNT) ht
  simp only [Real.toNNReal_coe] at h
  rw [h]
  congr 1
  · congr 1
    apply integral_congr_ae
    filter_upwards [ht] with s hs
    apply integral_congr_ae
    exact ae_of_all _ fun ω => by simp only [ν, past_integral_real T s hs]
  · apply integral_congr_ae
    filter_upwards [ht] with s hs
    apply integral_congr_ae
    exact ae_of_all _ fun ω => by simp only [ν, past_integral_real T s hs]

end LinearStochastic.RealTimeBridge
