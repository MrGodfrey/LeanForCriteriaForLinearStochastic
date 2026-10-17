module

public import LinearStochastic.DriftProductExpectation

@[expose] public section

noncomputable section
namespace LinearStochastic.DriftPairIntegrability
open MeasureTheory Set
open scoped InnerProductSpace
variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- H² drifts have an integrable actual terminal product. -/
theorem terminal_product_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    (P : Measure Ω) [IsFiniteMeasure P] (f g : ℝ → Ω → E)
    (hf : MemLp (Function.uncurry f) 2 (ν.prod P))
    (hg : MemLp (Function.uncurry g) 2 (ν.prod P)) :
    Integrable (fun ω => inner ℝ (∫ s, f s ω ∂ν) (∫ t, g t ω ∂ν)) P := by
  have hh := DriftProductExpectation.cross_product_integrable ν P f g hf hg
  have hp : Integrable (fun z : (ℝ × ℝ) × Ω =>
      inner ℝ (f z.1.1 z.2) (g z.1.2 z.2)) ((ν.prod ν).prod P) :=
    (measurePreserving_prodAssoc ν ν P).integrable_comp_of_integrable hh
  apply hp.integral_prod_right.congr
  filter_upwards [(hf.integrable one_le_two).prod_left_ae,
    (hg.integrable one_le_two).prod_left_ae, hp.prod_left_ae] with ω hfw hgw hi
  dsimp only [Function.uncurry] at hfw hgw
  rw [integral_prod _ hi, integral_integral_swap hi]
  calc
    _ = ∫ t, inner ℝ (∫ s, f s ω ∂ν) (g t ω) ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ fun t => ((innerSL ℝ).flip (g t ω)).integral_comp_comm hfw
    _ = _ := integral_inner (𝕜 := ℝ) hgw (∫ s, f s ω ∂ν)

/-- Pairing a pathwise H² drift integral with any genuine L² terminal variable
is integrable, with no adaptedness or martingale premise required. -/
theorem terminal_cross_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    (P : Measure Ω) [IsFiniteMeasure P] (f : ℝ → Ω → E) (Y : Ω → E)
    (hf : MemLp (Function.uncurry f) 2 (ν.prod P)) (hY : MemLp Y 2 P) :
    Integrable (fun ω => inner ℝ (∫ s, f s ω ∂ν) (Y ω)) P := by
  have hp : Integrable (fun z : ℝ × Ω => inner ℝ (f z.1 z.2) (Y z.2)) (ν.prod P) :=
    DriftMartingaleDuality.integrable_inner_of_memLp hf (hY.comp_snd ν)
  apply hp.integral_prod_right.congr
  filter_upwards [(hf.integrable one_le_two).prod_left_ae] with ω hfw
  exact ((innerSL ℝ).flip (Y ω)).integral_comp_comm hfw

/-- Each past-primitive pairing is integrable in the sample coordinate, and
its expectation equals the genuine past integral of two-time expectations. -/
theorem past_pair_sections (ν : Measure ℝ) [IsFiniteMeasure ν]
    (P : Measure Ω) [IsFiniteMeasure P] (f g : ℝ → Ω → E)
    (hf : MemLp (Function.uncurry f) 2 (ν.prod P))
    (hg : MemLp (Function.uncurry g) 2 (ν.prod P)) :
    ∀ᵐ s ∂ν,
      Integrable (fun ω => inner ℝ (f s ω) (∫ t in Iic s, g t ω ∂ν)) P ∧
      (∫ ω, inner ℝ (f s ω) (∫ t in Iic s, g t ω ∂ν) ∂P) =
        ∫ t in Iic s, ∫ ω, inner ℝ (f s ω) (g t ω) ∂P ∂ν := by
  have hh := DriftProductExpectation.cross_product_integrable ν P f g hf hg
  have hgp := (hg.integrable one_le_two).prod_left_ae
  filter_upwards [hh.prod_right_ae] with s hs
  have hi : Integrable (fun z : ℝ × Ω => inner ℝ (f s z.2) (g z.1 z.2))
      ((ν.restrict (Iic s)).prod P) :=
    hs.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have he : (fun ω => ∫ t in Iic s, inner ℝ (f s ω) (g t ω) ∂ν) =ᵐ[P]
      fun ω => inner ℝ (f s ω) (∫ t in Iic s, g t ω ∂ν) := by
    filter_upwards [hgp] with ω hgw
    exact integral_inner (𝕜 := ℝ) hgw.integrableOn (f s ω)
  exact ⟨hi.integral_prod_right.congr he,
    (integral_congr_ae he).symm.trans (integral_integral_swap hi).symm⟩

/-- The expectations of the past-primitive pairings are time-integrable. -/
theorem past_pair_expectation_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    (P : Measure Ω) [IsFiniteMeasure P] (f g : ℝ → Ω → E)
    (hf : MemLp (Function.uncurry f) 2 (ν.prod P))
    (hg : MemLp (Function.uncurry g) 2 (ν.prod P)) :
    Integrable (fun s => ∫ ω, inner ℝ (f s ω) (∫ t in Iic s, g t ω ∂ν) ∂P) ν := by
  have hh := DriftProductExpectation.cross_product_integrable ν P f g hf hg
  have hp : Integrable (fun z : (ℝ × ℝ) × Ω =>
      inner ℝ (f z.1.1 z.2) (g z.1.2 z.2)) ((ν.prod ν).prod P) :=
    (measurePreserving_prodAssoc ν ν P).integrable_comp_of_integrable hh
  let h : ℝ × ℝ → ℝ := fun z => ∫ ω, inner ℝ (f z.1 ω) (g z.2 ω) ∂P
  let L : Set (ℝ × ℝ) := {z | z.2 ≤ z.1}
  have hL : MeasurableSet L := measurableSet_le measurable_snd measurable_fst
  have hi : Integrable (L.indicator h) (ν.prod ν) := hp.integral_prod_left.indicator hL
  apply hi.integral_prod_left.congr
  filter_upwards [past_pair_sections ν P f g hf hg] with s hs
  calc
    _ = ∫ t in Iic s, ∫ ω, inner ℝ (f s ω) (g t ω) ∂P ∂ν := by
      rw [← integral_indicator measurableSet_Iic]
      apply integral_congr_ae
      exact ae_of_all _ fun t => by simp [L, h, indicator_apply]
    _ = _ := hs.2.symm

/-- For actual martingales, conditional pull-out proves both sample
integrability and expectation equality at almost every drift time. -/
theorem martingale_pair_sections (ν : Measure ℝ) [IsFiniteMeasure ν]
    (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration ℝ mΩ) (M : ℝ → Ω → E) (hM : Martingale M 𝓕 P)
    (f : ℝ → Ω → E) (hf : MemLp (Function.uncurry f) 2 (ν.prod P))
    (hadapt : ∀ᵐ s ∂ν, AEStronglyMeasurable[𝓕 s] (f s) P)
    (T : ℝ) (hMT : MemLp (M T) 2 P) (hT : ∀ᵐ s ∂ν, s ≤ T) :
    ∀ᵐ s ∂ν, Integrable (fun ω => inner ℝ (f s ω) (M s ω)) P ∧
      (∫ ω, inner ℝ (f s ω) (M s ω) ∂P) =
        ∫ ω, inner ℝ (f s ω) (M T ω) ∂P := by
  have hp : Integrable (fun z : ℝ × Ω => inner ℝ (f z.1 z.2) (M T z.2)) (ν.prod P) :=
    DriftMartingaleDuality.integrable_inner_of_memLp hf (hMT.comp_snd ν)
  filter_upwards [hp.prod_right_ae, hadapt, hT] with s hi hs ht
  have he := condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ)
    hs hi (hMT.integrable one_le_two)
  have he' : P[fun ω => inner ℝ (f s ω) (M T ω) | 𝓕 s] =ᵐ[P]
      fun ω => inner ℝ (f s ω) (M s ω) := by
    filter_upwards [he, hM.2 s T ht] with ω he hMω
    exact he.trans (congrArg (fun x => inner ℝ (f s ω) x) hMω)
  exact ⟨integrable_condExp.congr he',
    (integral_congr_ae he').symm.trans (integral_condExp (𝓕.le s))⟩

/-- The contemporaneous martingale pairing expectations are integrable in time. -/
theorem martingale_pair_expectation_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration ℝ mΩ) (M : ℝ → Ω → E) (hM : Martingale M 𝓕 P)
    (f : ℝ → Ω → E) (hf : MemLp (Function.uncurry f) 2 (ν.prod P))
    (hadapt : ∀ᵐ s ∂ν, AEStronglyMeasurable[𝓕 s] (f s) P)
    (T : ℝ) (hMT : MemLp (M T) 2 P) (hT : ∀ᵐ s ∂ν, s ≤ T) :
    Integrable (fun s => ∫ ω, inner ℝ (f s ω) (M s ω) ∂P) ν := by
  have hp : Integrable (fun z : ℝ × Ω => inner ℝ (f z.1 z.2) (M T z.2)) (ν.prod P) :=
    DriftMartingaleDuality.integrable_inner_of_memLp hf (hMT.comp_snd ν)
  apply hp.integral_prod_left.congr
  exact (martingale_pair_sections ν P 𝓕 M hM f hf hadapt T hMT hT).mono
    (fun s hs => hs.2.symm)

#print axioms terminal_product_integrable
#print axioms past_pair_expectation_integrable
#print axioms martingale_pair_sections
end LinearStochastic.DriftPairIntegrability
