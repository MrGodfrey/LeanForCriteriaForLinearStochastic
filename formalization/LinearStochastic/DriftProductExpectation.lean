module

public import LinearStochastic.DriftMartingaleDuality
public import LinearStochastic.DriftProduct

@[expose] public section

noncomputable section
namespace LinearStochastic.DriftProductExpectation
open MeasureTheory Set
open scoped InnerProductSpace

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Independent time coordinates may be permuted without changing their
product measure, while the sample coordinate stays fixed. -/
theorem time_swap_preserving (ν : Measure ℝ) [SFinite ν] (P : Measure Ω) [SFinite P] :
    MeasurePreserving (fun z : ℝ × (ℝ × Ω) => (z.2.1,(z.1,z.2.2)))
      (ν.prod (ν.prod P)) (ν.prod (ν.prod P)) := by
  have ha := measurePreserving_prodAssoc ν ν P
  have hs := (Measure.measurePreserving_swap (μ := ν) (ν := ν)).prod (MeasurePreserving.id P)
  have hh := ha.comp (hs.comp ha.symm)
  exact hh

omit [CompleteSpace E] in
/-- Spacetime H² alone makes the shared-sample, two-time drift pairing
integrable. This is the genuine triple-measure Fubini obligation. -/
theorem cross_product_integrable (ν : Measure ℝ) [IsFiniteMeasure ν]
    (P : Measure Ω) [SFinite P] (f g : ℝ → Ω → E)
    (hf : MemLp (Function.uncurry f) 2 (ν.prod P))
    (hg : MemLp (Function.uncurry g) 2 (ν.prod P)) :
    Integrable (fun z : ℝ × (ℝ × Ω) => inner ℝ (f z.1 z.2.2) (g z.2.1 z.2.2))
      (ν.prod (ν.prod P)) := by
  have hflift : MemLp (fun z : ℝ × (ℝ × Ω) => f z.1 z.2.2) 2 (ν.prod (ν.prod P)) :=
    (hf.comp_snd ν).comp_measurePreserving (time_swap_preserving ν P)
  exact DriftMartingaleDuality.integrable_inner_of_memLp hflift (hg.comp_snd ν)

/-- The expected terminal product of actual pathwise drift integrals is the
integral of their shared-sample two-time pairing. All Fubini hypotheses are
derived from the two spacetime H² assumptions. -/
theorem terminal_drift_product (ν : Measure ℝ) [IsFiniteMeasure ν]
    (P : Measure Ω) [IsFiniteMeasure P] (f g : ℝ → Ω → E)
    (hf : MemLp (Function.uncurry f) 2 (ν.prod P))
    (hg : MemLp (Function.uncurry g) 2 (ν.prod P)) :
    (∫ ω, inner ℝ (∫ s, f s ω ∂ν) (∫ t, g t ω ∂ν) ∂P) =
      ∫ s, ∫ t, ∫ ω, inner ℝ (f s ω) (g t ω) ∂P ∂ν ∂ν := by
  have hh := cross_product_integrable ν P f g hf hg
  have hpair : Integrable (fun z : (ℝ × ℝ) × Ω =>
      inner ℝ (f z.1.1 z.2) (g z.1.2 z.2)) ((ν.prod ν).prod P) :=
    (measurePreserving_prodAssoc ν ν P).integrable_comp_of_integrable hh
  have hfp := (hf.integrable one_le_two).prod_left_ae
  have hgp := (hg.integrable one_le_two).prod_left_ae
  calc
    _ = ∫ ω, ∫ z : ℝ × ℝ, inner ℝ (f z.1 ω) (g z.2 ω) ∂(ν.prod ν) ∂P := by
      apply integral_congr_ae
      filter_upwards [hfp, hgp, hpair.prod_left_ae] with ω hfw hgw hi
      dsimp only [Function.uncurry] at hfw hgw
      rw [integral_prod _ hi]
      rw [← integral_inner (𝕜 := ℝ) hgw (∫ s, f s ω ∂ν)]
      rw [integral_integral_swap hi]
      apply integral_congr_ae
      exact ae_of_all _ fun t =>
        (((innerSL ℝ).flip (g t ω)).integral_comp_comm hfw).symm
    _ = ∫ z : ℝ × ℝ, ∫ ω, inner ℝ (f z.1 ω) (g z.2 ω) ∂P ∂(ν.prod ν) :=
      (integral_integral_swap hpair).symm
    _ = _ := integral_prod _ hpair.integral_prod_left

/-- Fubini exchanges the actual past-time integral and expectation. The
integrability of every required restricted section follows from H². -/
theorem past_cross_expectation (ν : Measure ℝ) [IsFiniteMeasure ν]
    (P : Measure Ω) [IsFiniteMeasure P] (f g : ℝ → Ω → E)
    (hf : MemLp (Function.uncurry f) 2 (ν.prod P))
    (hg : MemLp (Function.uncurry g) 2 (ν.prod P)) :
    (∫ s, ∫ t in Iic s, ∫ ω, inner ℝ (f s ω) (g t ω) ∂P ∂ν ∂ν) =
      ∫ s, ∫ ω, inner ℝ (f s ω) (∫ t in Iic s, g t ω ∂ν) ∂P ∂ν := by
  have hh := cross_product_integrable ν P f g hf hg
  have hgp := (hg.integrable one_le_two).prod_left_ae
  apply integral_congr_ae
  filter_upwards [hh.prod_right_ae] with s hs
  have hi : Integrable (fun z : ℝ × Ω => inner ℝ (f s z.2) (g z.1 z.2))
      ((ν.restrict (Iic s)).prod P) :=
    hs.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  calc
    _ = ∫ ω, ∫ t in Iic s, inner ℝ (f s ω) (g t ω) ∂ν ∂P := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hgp] with ω hgw
      exact integral_inner (𝕜 := ℝ) hgw.integrableOn (f s ω)

/-- Raw-process expectation product formula for two spacetime-H² drifts.
There is no pre-assumed product identity, no extra Fubini hypothesis, and
no change to arbitrary representatives of the pathwise integrals. -/
theorem drift_product_expectation (ν : Measure ℝ) [IsFiniteMeasure ν] [NullSingletonClass ν]
    (P : Measure Ω) [IsFiniteMeasure P] (f g : ℝ → Ω → E)
    (hf : MemLp (Function.uncurry f) 2 (ν.prod P))
    (hg : MemLp (Function.uncurry g) 2 (ν.prod P)) :
    (∫ ω, inner ℝ (∫ s, f s ω ∂ν) (∫ t, g t ω ∂ν) ∂P) =
      (∫ s, ∫ ω, inner ℝ (f s ω) (∫ t in Iic s, g t ω ∂ν) ∂P ∂ν) +
      (∫ s, ∫ ω, inner ℝ (∫ t in Iic s, f t ω ∂ν) (g s ω) ∂P ∂ν) := by
  have hh := cross_product_integrable ν P f g hf hg
  have hpair : Integrable (fun z : (ℝ × ℝ) × Ω =>
      inner ℝ (f z.1.1 z.2) (g z.1.2 z.2)) ((ν.prod ν).prod P) :=
    (measurePreserving_prodAssoc ν ν P).integrable_comp_of_integrable hh
  rw [terminal_drift_product ν P f g hf hg]
  rw [DriftProduct.integral_order_triangles ν _ hpair.integral_prod_left]
  rw [past_cross_expectation ν P f g hf hg]
  congr 1
  calc
    _ = ∫ s, ∫ t in Iic s, ∫ ω, inner ℝ (g s ω) (f t ω) ∂P ∂ν ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ fun s => by
        dsimp only
        rw [← integral_Iic_eq_integral_Iio]
        apply integral_congr_ae
        exact ae_of_all _ fun t => integral_congr_ae (ae_of_all _ fun ω => real_inner_comm _ _)
    _ = ∫ s, ∫ ω, inner ℝ (g s ω) (∫ t in Iic s, f t ω ∂ν) ∂P ∂ν :=
      past_cross_expectation ν P g f hg hf
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ fun s => integral_congr_ae (ae_of_all _ fun ω => real_inner_comm _ _)

#print axioms terminal_drift_product
#print axioms drift_product_expectation
#print axioms cross_product_integrable
end LinearStochastic.DriftProductExpectation
