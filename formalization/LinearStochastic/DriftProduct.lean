import Mathlib

noncomputable section
namespace LinearStochastic.DriftProduct
open MeasureTheory Set
open scoped InnerProductSpace

/-- Fubini on the two actual order triangles. The diagonal is assigned to the
first triangle, so no non-atomic hypothesis is needed at this stage. -/
theorem integral_order_triangles (ν : Measure ℝ) [SFinite ν]
    (h : ℝ × ℝ → ℝ) (hh : Integrable h (ν.prod ν)) :
    (∫ s, ∫ t, h (s,t) ∂ν ∂ν) =
      (∫ s, ∫ t in Iic s, h (s,t) ∂ν ∂ν) +
      (∫ t, ∫ s in Iio t, h (s,t) ∂ν ∂ν) := by
  let L : Set (ℝ × ℝ) := {z | z.2 ≤ z.1}
  have hL : MeasurableSet L := measurableSet_le measurable_snd measurable_fst
  have hi : Integrable (L.indicator h) (ν.prod ν) := hh.indicator hL
  have hc : Integrable (Lᶜ.indicator h) (ν.prod ν) := hh.indicator hL.compl
  have hsplit : h = L.indicator h + Lᶜ.indicator h := by
    funext z
    by_cases hz : z ∈ L <;> simp [hz]
  calc
    _ = ∫ z, h z ∂(ν.prod ν) := (integral_prod h hh).symm
    _ = (∫ z, L.indicator h z ∂(ν.prod ν)) +
        ∫ z, Lᶜ.indicator h z ∂(ν.prod ν) := by
      calc
        _ = ∫ z, (L.indicator h + Lᶜ.indicator h) z ∂(ν.prod ν) := congrArg (fun f => ∫ z, f z ∂(ν.prod ν)) hsplit
        _ = _ := integral_add hi hc
    _ = _ := by
      rw [integral_prod _ hi, integral_prod_symm _ hc]
      congr 1
      · apply integral_congr_ae
        exact ae_of_all _ fun s => by
          dsimp only
          rw [← integral_indicator measurableSet_Iic]
          apply integral_congr_ae
          exact ae_of_all _ fun t => by simp [L, indicator_apply]
      · apply integral_congr_ae
        exact ae_of_all _ fun t => by
          dsimp only
          rw [← integral_indicator measurableSet_Iio]
          apply integral_congr_ae
          exact ae_of_all _ fun s => by simp [L, indicator_apply, not_le]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Each primitive cross term is actually integrable, before any integral
identity is used. This prevents totalized nonintegrable integrals from hiding
an integrability obligation. -/
theorem primitive_cross_integrable (ν : Measure ℝ) [SFinite ν]
    (f g : ℝ → E) (hf : Integrable f ν) (hg : Integrable g ν) :
    Integrable (fun s => inner ℝ (f s) (∫ t in Iic s, g t ∂ν)) ν := by
  let h : ℝ × ℝ → ℝ := fun z => inner ℝ (f z.1) (g z.2)
  have hprod : Integrable h (ν.prod ν) :=
    hf.op_fst_snd (continuous_inner (𝕜 := ℝ))
      ⟨1, by intro x y; simpa using norm_inner_le_norm (𝕜 := ℝ) x y⟩ hg
  let L : Set (ℝ × ℝ) := {z | z.2 ≤ z.1}
  have hL : MeasurableSet L := measurableSet_le measurable_snd measurable_fst
  apply ((hprod.indicator hL).integral_prod_left).congr
  exact ae_of_all _ fun s => by
    dsimp only
    calc
      (∫ t, L.indicator h (s,t) ∂ν) = ∫ t in Iic s, inner ℝ (f s) (g t) ∂ν := by
        rw [← integral_indicator measurableSet_Iic]
        apply integral_congr_ae
        exact ae_of_all _ fun t => by simp [L, h, indicator_apply]
      _ = _ := integral_inner hg.integrableOn (f s)

theorem primitive_cross_integrable_left (ν : Measure ℝ) [SFinite ν]
    (f g : ℝ → E) (hf : Integrable f ν) (hg : Integrable g ν) :
    Integrable (fun s => inner ℝ (∫ t in Iic s, f t ∂ν) (g s)) ν := by
  apply (primitive_cross_integrable ν g f hg hf).congr
  exact ae_of_all _ fun s => real_inner_comm _ _

/-- True Bochner product formula for two integrable drifts. Non-atomic time
makes their common diagonal negligible; no derivative or desired identity
is assumed. Finite Lebesgue intervals are instances by restriction. -/
theorem inner_integral_product (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    (f g : ℝ → E) (hf : Integrable f ν) (hg : Integrable g ν) :
    inner ℝ (∫ s, f s ∂ν) (∫ s, g s ∂ν) =
      (∫ s, inner ℝ (f s) (∫ t in Iic s, g t ∂ν) ∂ν) +
      (∫ s, inner ℝ (∫ t in Iic s, f t ∂ν) (g s) ∂ν) := by
  have hprod : Integrable (fun z : ℝ × ℝ => inner ℝ (f z.1) (g z.2)) (ν.prod ν) :=
    hf.op_fst_snd (continuous_inner (𝕜 := ℝ)) ⟨1, by intro x y; simpa using norm_inner_le_norm (𝕜 := ℝ) x y⟩ hg
  calc
    _ = ∫ s, ∫ t, inner ℝ (f s) (g t) ∂ν ∂ν := by
      rw [← integral_inner hg (∫ s, f s ∂ν)]
      rw [integral_integral_swap hprod]
      apply integral_congr_ae
      exact ae_of_all _ fun s => by
        exact (((innerSL ℝ).flip (g s)).integral_comp_comm hf).symm
    _ = (∫ s, ∫ t in Iic s, inner ℝ (f s) (g t) ∂ν ∂ν) +
        ∫ t, ∫ s in Iio t, inner ℝ (f s) (g t) ∂ν ∂ν :=
      integral_order_triangles ν _ hprod
    _ = _ := by
      congr 1
      · apply integral_congr_ae
        exact ae_of_all _ fun s => integral_inner hg.integrableOn (f s)
      · apply integral_congr_ae
        exact ae_of_all _ fun s => by
          dsimp only
          rw [← integral_Iic_eq_integral_Iio]
          exact ((innerSL ℝ).flip (g s)).integral_comp_comm hf.integrableOn

/-- The same identity on the actual finite interval, with each primitive
restricted to the part of that interval before the current time. -/
theorem inner_integral_product_Ioc (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    (a b : ℝ) (f g : ℝ → E) (hf : IntegrableOn f (Ioc a b) ν)
    (hg : IntegrableOn g (Ioc a b) ν) :
    inner ℝ (∫ s in Ioc a b, f s ∂ν) (∫ s in Ioc a b, g s ∂ν) =
      (∫ s in Ioc a b, inner ℝ (f s) (∫ t in Ioc a s, g t ∂ν) ∂ν) +
      (∫ s in Ioc a b, inner ℝ (∫ t in Ioc a s, f t ∂ν) (g s) ∂ν) := by
  rw [inner_integral_product (ν.restrict (Ioc a b)) f g hf hg]
  congr 1
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioc_of_le hs.2]
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioc_of_le hs.2]

/-- A literal expectation identity in the actual Hilbert space of L² random
variables. The time integrals here are Bochner integrals in that space;
this theorem does not assert a pointwise representative or continuity. -/
theorem l2_expected_drift_product {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ν : Measure ℝ) [SFinite ν] [NullSingletonClass ν]
    (F G : ℝ → Lp E 2 P) (hF : Integrable F ν) (hG : Integrable G ν) :
    (∫ ω, inner ℝ ((∫ s, F s ∂ν) ω) ((∫ s, G s ∂ν) ω) ∂P) =
      (∫ s, ∫ ω, inner ℝ (F s ω) ((∫ t in Iic s, G t ∂ν) ω) ∂P ∂ν) +
      (∫ s, ∫ ω, inner ℝ ((∫ t in Iic s, F t ∂ν) ω) (G s ω) ∂P ∂ν) := by
  simpa only [L2.inner_def] using inner_integral_product ν F G hF hG

#print axioms inner_integral_product_Ioc
#print axioms l2_expected_drift_product
#print axioms inner_integral_product
end LinearStochastic.DriftProduct
