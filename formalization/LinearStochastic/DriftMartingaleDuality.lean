import Mathlib

/-!
# The expectation cross term between a Bochner drift and a genuine L² martingale

The conditional expectation is Mathlib's actual L² orthogonal projection.
The drift integral is a Bochner integral of L² random variables. No stochastic
integral or desired duality identity is postulated.
-/
noncomputable section
namespace LinearStochastic.DriftMartingaleDuality
open MeasureTheory
open scoped ENNReal InnerProductSpace

variable {Ω E I : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- An adapted L² variable pairs against a conditional expectation exactly as
it pairs against the original terminal variable. -/
theorem adapted_pairing_condExp (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (F Y : Lp E 2 P) (hF : AEStronglyMeasurable[m] F P) :
    inner ℝ F (condExpL2 E ℝ hm Y : Lp E 2 P) = inner ℝ F Y := by
  calc
    _ = inner ℝ (condExpL2 E ℝ hm Y : Lp E 2 P) F := real_inner_comm _ _
    _ = inner ℝ Y F := inner_condExpL2_eq_inner_fun hm Y F hF
    _ = _ := real_inner_comm _ _

/-- Integrating the actual L² conditional pairing in time. -/
theorem bochner_drift_pairing [MeasurableSpace I] (ν : Measure I)
    (m : I → MeasurableSpace Ω) (hm : ∀ s, m s ≤ mΩ)
    (F : I → Lp E 2 P) (hF : Integrable F ν)
    (hadapt : ∀ᵐ s ∂ν, AEStronglyMeasurable[m s] (F s) P)
    (Y : Lp E 2 P) :
    inner ℝ (∫ s, F s ∂ν) Y =
      ∫ s, inner ℝ (F s) (condExpL2 E ℝ (hm s) Y : Lp E 2 P) ∂ν := by
  calc
    inner ℝ (∫ s, F s ∂ν) Y = ∫ s, inner ℝ (F s) Y ∂ν := by
      rw [real_inner_comm, ← integral_inner hF Y]
      exact integral_congr_ae (ae_of_all _ fun s => (real_inner_comm Y (F s)).symm)
    _ = _ := integral_congr_ae (hadapt.mono fun s hs =>
      (adapted_pairing_condExp (m s) (hm s) (F s) Y hs).symm)

section Martingale
variable [Preorder I] [IsFiniteMeasure P]

/-- A genuine martingale's earlier L² class is the actual conditional
expectation of its terminal class. -/
theorem martingale_condExpL2 (𝓕 : Filtration I mΩ) (M : I → Ω → E)
    (hM : Martingale M 𝓕 P) (hM2 : ∀ s, MemLp (M s) 2 P)
    (s t : I) (hst : s ≤ t) :
    (condExpL2 E ℝ (𝓕.le s) ((hM2 t).toLp (M t)) : Lp E 2 P) =
      (hM2 s).toLp (M s) := by
  apply Lp.ext
  exact ((hM2 t).condExpL2_ae_eq_condExp (𝕜 := ℝ) (𝓕.le s)).trans
    ((hM.2 s t hst).trans (hM2 s).coeFn_toLp.symm)

/-- The drift--martingale cross identity, for an actual martingale and
adapted Bochner-integrable L² drift random variables. The time measure may
be any finite-horizon restriction supported before the terminal time. -/
theorem drift_martingale_cross [MeasurableSpace I] (ν : Measure I)
    (𝓕 : Filtration I mΩ) (M : I → Ω → E)
    (hM : Martingale M 𝓕 P) (hM2 : ∀ s, MemLp (M s) 2 P)
    (F : I → Lp E 2 P) (hF : Integrable F ν)
    (hadapt : ∀ᵐ s ∂ν, AEStronglyMeasurable[𝓕 s] (F s) P)
    (T : I) (hT : ∀ᵐ s ∂ν, s ≤ T) :
    inner ℝ (∫ s, F s ∂ν) ((hM2 T).toLp (M T)) =
      ∫ s, inner ℝ (F s) ((hM2 s).toLp (M s)) ∂ν := by
  rw [bochner_drift_pairing ν (fun s => 𝓕 s) (fun s => 𝓕.le s) F hF hadapt]
  apply integral_congr_ae
  filter_upwards [hT] with s hs
  rw [martingale_condExpL2 𝓕 M hM hM2 s T hs]

end Martingale
omit [CompleteSpace E] in
/-- Genuine L² random variables have an integrable pointwise inner product. -/
theorem integrable_inner_of_memLp {f g : Ω → E}
    (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => inner ℝ (f ω) (g ω)) P := by
  apply (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
  rw [h1, h2]

/-- Direct process-level drift--martingale cross identity. The drift has the
paper's actual spacetime L² integrability, and Fubini and the conditional
pull-out property are proved applicable from that assumption. -/
theorem drift_martingale_cross_expectation
    [MeasurableSpace I] [Preorder I] [IsFiniteMeasure P]
    (ν : Measure I) [IsFiniteMeasure ν]
    (𝓕 : Filtration I mΩ) (M : I → Ω → E) (hM : Martingale M 𝓕 P)
    (f : I → Ω → E) (hf : MemLp (Function.uncurry f) 2 (ν.prod P))
    (hadapt : ∀ᵐ s ∂ν, AEStronglyMeasurable[𝓕 s] (f s) P)
    (T : I) (hMT : MemLp (M T) 2 P) (hT : ∀ᵐ s ∂ν, s ≤ T) :
    (∫ ω, inner ℝ (∫ s, f s ω ∂ν) (M T ω) ∂P) =
      ∫ s, ∫ ω, inner ℝ (f s ω) (M s ω) ∂P ∂ν := by
  have hprod : Integrable (fun z : I × Ω => inner ℝ (f z.1 z.2) (M T z.2))
      (ν.prod P) := integrable_inner_of_memLp hf (hMT.comp_snd ν)
  have hpath : ∀ᵐ ω ∂P, Integrable (fun s => f s ω) ν :=
    (hf.integrable one_le_two).prod_left_ae
  calc
    _ = ∫ ω, ∫ s, inner ℝ (f s ω) (M T ω) ∂ν ∂P := by
      apply integral_congr_ae
      filter_upwards [hpath] with ω hω
      exact (((innerSL ℝ).flip (M T ω)).integral_comp_comm hω).symm
    _ = ∫ s, ∫ ω, inner ℝ (f s ω) (M T ω) ∂P ∂ν :=
      (integral_integral_swap hprod).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hadapt, hT, hprod.prod_right_ae] with s hfs hs hint
      have hpull := condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ)
        hfs hint (hMT.integrable one_le_two)
      calc
        _ = ∫ ω, P[fun ω => inner ℝ (f s ω) (M T ω) | 𝓕 s] ω ∂P :=
          (integral_condExp (𝓕.le s)).symm
        _ = ∫ ω, inner ℝ (f s ω) (P[M T | 𝓕 s] ω) ∂P :=
          integral_congr_ae hpull
        _ = _ := integral_congr_ae ((hM.2 s T hs).mono fun ω hω =>
          congrArg (fun x => inner ℝ (f s ω) x) hω)

#print axioms drift_martingale_cross_expectation
end LinearStochastic.DriftMartingaleDuality
