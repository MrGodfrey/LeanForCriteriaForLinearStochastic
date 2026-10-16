import LinearStochastic.LinearDuality

/-! Pointwise deterministic Lyapunov inequalities integrated on actual L²
state classes. All quadratic integrability is proved from the L² data. -/
noncomputable section
namespace LinearStochastic.LpLyapunovEstimate
open MeasureTheory
open scoped InnerProductSpace BigOperators
variable {Λ E ι : Type*} {mΛ : MeasurableSpace Λ} {ν : Measure Λ}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]

theorem quadratic_integrable (H : E →L[ℝ] E) (X : Lp E 2 ν) :
    Integrable (fun z => inner ℝ (X z) (H (X z))) ν :=
  DriftMartingaleDuality.integrable_inner_of_memLp (Lp.memLp X) (H.comp_memLp X)

theorem quadratic_inner (H : E →L[ℝ] E) (X : Lp E 2 ν) :
    inner ℝ X (H.compLp X) = ∫ z, inner ℝ (X z) (H (X z)) ∂ν := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [H.coeFn_compLp X] with z h
  rw [h]

theorem coefficient_inner (H A : E →L[ℝ] E) (X : Lp E 2 ν) :
    inner ℝ (A.compLp X) (H.compLp X) = ∫ z, inner ℝ (A (X z)) (H (X z)) ∂ν := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [H.coeFn_compLp X,A.coeFn_compLp X] with z h a
  rw [h,a]

theorem diffusion_inner (H C : E →L[ℝ] E) (X : Lp E 2 ν) :
    inner ℝ (C.compLp X) (H.compLp (C.compLp X)) =
      ∫ z, inner ℝ (C (X z)) (H (C (X z))) ∂ν := by
  rw [quadratic_inner]
  apply integral_congr_ae
  filter_upwards [C.coeFn_compLp X] with z h
  rw [h]

/-- A true pointwise Lyapunov inequality yields the actual quadratic drift
and diffusion bound for every square-integrable state. -/
theorem integrated (H A : E →L[ℝ] E) (C : ι → E →L[ℝ] E) (ρ : ℝ)
    (hq : ∀ x, (∑ i, inner ℝ (C i x) (H (C i x))) +
      2 * inner ℝ (A x) (H x) ≤ -ρ * inner ℝ x (H x)) (X : Lp E 2 ν) :
    (∑ i, inner ℝ ((C i).compLp X) (H.compLp ((C i).compLp X))) +
      2 * inner ℝ (A.compLp X) (H.compLp X) ≤ -ρ * inner ℝ X (H.compLp X) := by
  have hd (i) : Integrable (fun z => inner ℝ (C i (X z)) (H (C i (X z)))) ν :=
    DriftMartingaleDuality.integrable_inner_of_memLp ((C i).comp_memLp X)
      (H.comp_memLp' ((C i).comp_memLp X))
  have ha : Integrable (fun z => inner ℝ (A (X z)) (H (X z))) ν :=
    DriftMartingaleDuality.integrable_inner_of_memLp (A.comp_memLp X) (H.comp_memLp X)
  have hi := integral_mono ((integrable_finsetSum Finset.univ (fun i _ => hd i)).add
    (ha.const_mul 2)) ((quadratic_integrable H X).const_mul (-ρ)) (fun z => hq (X z))
  simp only [Pi.add_apply] at hi
  rw [integral_add (integrable_finsetSum Finset.univ (fun i _ => hd i)) (ha.const_mul 2),
    integral_finsetSum _ (fun i _ => hd i), integral_const_mul, integral_const_mul] at hi
  simp_rw [diffusion_inner, coefficient_inner, quadratic_inner]
  exact hi

end LinearStochastic.LpLyapunovEstimate
