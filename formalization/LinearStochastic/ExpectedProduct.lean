module

public import LinearStochastic.DriftPairIntegrability

@[expose] public section

/-!
# Expected product of H² drifts and genuine martingales

This identity uses actual pathwise Bochner integrals and actual martingale
conditional expectations. The terminal martingale covariance remains explicit;
an Itô covariance theorem is needed to identify it for stochastic integrals.
-/
noncomputable section
namespace LinearStochastic.ExpectedProduct
open MeasureTheory Set
open scoped InnerProductSpace
open DriftPairIntegrability

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The expected pairing of a drift with a past drift plus a contemporaneous
martingale splits into two actual integrable terms. -/
theorem drift_state_pairing (ν : Measure ℝ) [IsFiniteMeasure ν]
    (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration ℝ mΩ) (N : ℝ → Ω → E) (hN : Martingale N 𝓕 P)
    (f g : ℝ → Ω → E)
    (hf : MemLp (Function.uncurry f) 2 (ν.prod P))
    (hg : MemLp (Function.uncurry g) 2 (ν.prod P))
    (hadapt : ∀ᵐ s ∂ν, AEStronglyMeasurable[𝓕 s] (f s) P)
    (T : ℝ) (hNT : MemLp (N T) 2 P) (hT : ∀ᵐ s ∂ν, s ≤ T) :
    (∫ s, ∫ ω, inner ℝ (f s ω) ((∫ t in Iic s, g t ω ∂ν) + N s ω) ∂P ∂ν) =
      (∫ s, ∫ ω, inner ℝ (f s ω) (∫ t in Iic s, g t ω ∂ν) ∂P ∂ν) +
      (∫ s, ∫ ω, inner ℝ (f s ω) (N s ω) ∂P ∂ν) := by
  calc
    _ = ∫ s, (∫ ω, inner ℝ (f s ω) (∫ t in Iic s, g t ω ∂ν) ∂P) +
        (∫ ω, inner ℝ (f s ω) (N s ω) ∂P) ∂ν := by
      apply integral_congr_ae
      filter_upwards [past_pair_sections ν P f g hf hg,
        martingale_pair_sections ν P 𝓕 N hN f hf hadapt T hNT hT] with s hs hn
      simp_rw [inner_add_right]
      exact integral_add hs.1 hn.1
    _ = _ := integral_add (past_pair_expectation_integrable ν P f g hf hg)
      (martingale_pair_expectation_integrable ν P 𝓕 N hN f hf hadapt T hNT hT)

/-- An actual finite-measure expected product formula. The two drifts are
spacetime H² and adapted; M and N are genuine martingales with L² terminal
values. Atomless time makes the drift diagonal have zero measure. No expected
product identity or stochastic integral is postulated in the hypotheses. -/
theorem expected_product (ν : Measure ℝ) [IsFiniteMeasure ν] [NullSingletonClass ν]
    (P : Measure Ω) [IsFiniteMeasure P]
    (𝓕 : Filtration ℝ mΩ) (M N : ℝ → Ω → E)
    (hM : Martingale M 𝓕 P) (hN : Martingale N 𝓕 P)
    (f g : ℝ → Ω → E)
    (hf : MemLp (Function.uncurry f) 2 (ν.prod P))
    (hg : MemLp (Function.uncurry g) 2 (ν.prod P))
    (haf : ∀ᵐ s ∂ν, AEStronglyMeasurable[𝓕 s] (f s) P)
    (hag : ∀ᵐ s ∂ν, AEStronglyMeasurable[𝓕 s] (g s) P)
    (T : ℝ) (hMT : MemLp (M T) 2 P) (hNT : MemLp (N T) 2 P)
    (hT : ∀ᵐ s ∂ν, s ≤ T) :
    (∫ ω, inner ℝ ((∫ s, f s ω ∂ν) + M T ω)
      ((∫ s, g s ω ∂ν) + N T ω) ∂P) =
      (∫ ω, inner ℝ (M T ω) (N T ω) ∂P) +
      (∫ s, ∫ ω, inner ℝ (f s ω) ((∫ t in Iic s, g t ω ∂ν) + N s ω) ∂P ∂ν) +
      (∫ s, ∫ ω, inner ℝ ((∫ t in Iic s, f t ω ∂ν) + M s ω) (g s ω) ∂P ∂ν) := by
  have hfg := terminal_product_integrable ν P f g hf hg
  have hfn := terminal_cross_integrable ν P f (N T) hf hNT
  have hmg : Integrable (fun ω => inner ℝ (M T ω) (∫ s, g s ω ∂ν)) P := by
    simpa only [real_inner_comm] using terminal_cross_integrable ν P g (M T) hg hMT
  have hmn := DriftMartingaleDuality.integrable_inner_of_memLp hMT hNT
  have hmgE : (∫ ω, inner ℝ (M T ω) (∫ s, g s ω ∂ν) ∂P) =
      ∫ s, ∫ ω, inner ℝ (g s ω) (M s ω) ∂P ∂ν := by
    calc
      _ = ∫ ω, inner ℝ (∫ s, g s ω ∂ν) (M T ω) ∂P :=
        integral_congr_ae (ae_of_all _ fun ω => real_inner_comm _ _)
      _ = _ := DriftMartingaleDuality.drift_martingale_cross_expectation ν 𝓕 M hM g hg hag T hMT hT
  have hright : (∫ s, ∫ ω, inner ℝ ((∫ t in Iic s, f t ω ∂ν) + M s ω) (g s ω) ∂P ∂ν) =
      (∫ s, ∫ ω, inner ℝ (g s ω) (∫ t in Iic s, f t ω ∂ν) ∂P ∂ν) +
      (∫ s, ∫ ω, inner ℝ (g s ω) (M s ω) ∂P ∂ν) := by
    calc
      _ = ∫ s, ∫ ω, inner ℝ (g s ω) ((∫ t in Iic s, f t ω ∂ν) + M s ω) ∂P ∂ν := by
        apply integral_congr_ae
        exact ae_of_all _ fun s => integral_congr_ae (ae_of_all _ fun ω => real_inner_comm _ _)
      _ = _ := drift_state_pairing ν P 𝓕 M hM g f hg hf hag T hMT hT
  rw [drift_state_pairing ν P 𝓕 N hN f g hf hg haf T hNT hT, hright]
  calc
    _ = ((∫ ω, inner ℝ (∫ s, f s ω ∂ν) (∫ s, g s ω ∂ν) ∂P) +
          (∫ ω, inner ℝ (∫ s, f s ω ∂ν) (N T ω) ∂P)) +
        ((∫ ω, inner ℝ (M T ω) (∫ s, g s ω ∂ν) ∂P) +
          (∫ ω, inner ℝ (M T ω) (N T ω) ∂P)) := by
      simp_rw [inner_add_left, inner_add_right]
      have hfirst := integral_add hfg hfn
      have hsecond := integral_add hmg hmn
      have hsum := integral_add (hfg.add hfn) (hmg.add hmn)
      simp only [Pi.add_apply] at hsum hfirst hsecond
      rw [hsum, hfirst, hsecond]
    _ = _ := by
      rw [DriftProductExpectation.drift_product_expectation ν P f g hf hg,
        DriftMartingaleDuality.drift_martingale_cross_expectation ν 𝓕 N hN f hf haf T hNT hT,
        hmgE]
      have hcomm : (∫ s, ∫ ω, inner ℝ (∫ t in Iic s, f t ω ∂ν) (g s ω) ∂P ∂ν) =
          ∫ s, ∫ ω, inner ℝ (g s ω) (∫ t in Iic s, f t ω ∂ν) ∂P ∂ν := by
        apply integral_congr_ae
        exact ae_of_all _ fun s => integral_congr_ae (ae_of_all _ fun ω => real_inner_comm _ _)
      rw [hcomm]
      ring

#print axioms drift_state_pairing
#print axioms expected_product
end LinearStochastic.ExpectedProduct
