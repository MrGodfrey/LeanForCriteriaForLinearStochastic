module

public import LinearStochastic.JointDoleansBand
public import LinearStochastic.FiniteExponentialTotality

@[expose] public section

noncomputable section
namespace LinearStochastic.JointDoleansMoments
open MeasureTheory ProbabilityTheory CommonItoMultichannel
open scoped NNReal BigOperators
variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  (W : ι → ℝ≥0 → Ω → ℝ) (hW : ∀ i, IsPreBrownianReal (W i) μ)
  (hWm : ∀ i t, Measurable (W i t))

/-- The actual finite-coordinate stochastic exponential for a deterministic
step integrand on the given probability space. -/
def stepExp (s : ℕ → ℝ≥0) (v : ℕ → ι → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ Finset.range N, Real.exp ((∑ i, v k i * (W i (s (k+1)) ω - W i (s k) ω)) -
    (∑ i, v k i ^ 2) * ((s (k+1) : ℝ) - (s k : ℝ)) / 2)

include hW hWm in
/-- Finite vector increment exponentials have actual L² moments for all real
scales. This uses only genuine scalar Brownian Gaussian moments. -/
theorem memLp_exp_vector_increment (a b : ℝ≥0) (v : ι → ℝ) (c : ℝ) :
    MemLp (fun ω => Real.exp (c * ∑ i, v i * (W i b ω - W i a ω))) 2 μ :=
  FiniteExponentialTotality.memLp_exp_linear (fun i ω => W i b ω - W i a ω)
    (fun i => (hWm i b).sub (hWm i a))
    (fun i d => MathFin.memLp_exp_incr (hW i) a b d) v Finset.univ c

include hW hWm in
theorem memLp_exp_stepSum (s : ℕ → ℝ≥0) (v : ℕ → ι → ℝ) :
    ∀ n : ℕ, ∀ c : ℝ, MemLp (fun ω => Real.exp (c *
      ∑ k ∈ Finset.range n, ∑ i, v k i * (W i (s (k+1)) ω - W i (s k) ω))) 2 μ := by
  have hmeas (n : ℕ) (c : ℝ) : AEStronglyMeasurable (fun ω => Real.exp (c *
      ∑ k ∈ Finset.range n, ∑ i, v k i * (W i (s (k+1)) ω - W i (s k) ω))) μ := by
    apply Measurable.aestronglyMeasurable
    apply Real.measurable_exp.comp
    exact (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun i _ =>
      ((hWm i (s (k+1))).sub (hWm i (s k))).const_mul (v k i)).const_mul c
  intro n
  induction n with
  | zero => intro c; simpa using memLp_const (μ := μ) (1 : ℝ)
  | succ n ih =>
    intro c
    rw [memLp_two_iff_integrable_sq (hmeas (n+1) c)]
    have he : (fun ω => Real.exp (c * ∑ k ∈ Finset.range (n+1),
        ∑ i, v k i * (W i (s (k+1)) ω - W i (s k) ω)) ^ 2) =
        fun ω => Real.exp (2*c * ∑ k ∈ Finset.range n,
          ∑ i, v k i * (W i (s (k+1)) ω - W i (s k) ω)) *
          Real.exp (2*c * ∑ i, v n i * (W i (s (n+1)) ω - W i (s n) ω)) := by
      funext ω
      rw [Finset.sum_range_succ,sq,←Real.exp_add,←Real.exp_add]
      congr 1
      ring
    rw [he]
    exact (ih (2*c)).integrable_mul (memLp_exp_vector_increment W hW hWm (s n) (s (n+1)) (v n) (2*c))

include hW hWm in
theorem memLp_stepExp (s : ℕ → ℝ≥0) (v : ℕ → ι → ℝ) (n : ℕ) :
    MemLp (stepExp W s v n) 2 μ := by
  have he : stepExp W s v n = fun ω =>
      Real.exp (-∑ k ∈ Finset.range n, (∑ i, v k i ^ 2) * ((s (k+1) : ℝ) - (s k : ℝ)) / 2) *
      Real.exp (1 * ∑ k ∈ Finset.range n, ∑ i, v k i * (W i (s (k+1)) ω - W i (s k) ω)) := by
    funext ω
    simp only [stepExp]
    rw [←Real.exp_sum,Finset.sum_sub_distrib,one_mul,←Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (memLp_exp_stepSum W hW hWm s v n 1).const_mul _

theorem measurable_stepExp {s : ℕ → ℝ≥0} (hs : Monotone s) (v : ℕ → ι → ℝ) (n : ℕ) :
    Measurable[JointCylinderGeneration.natural W hWm (s n)] (stepExp W s v n) := by
  refine Finset.measurable_prod _ fun k hk => ?_
  have hk1 : k+1 ≤ n := Finset.mem_range.mp hk
  apply Real.measurable_exp.comp
  apply Measurable.sub _ measurable_const
  exact Finset.measurable_sum _ fun i _ =>
    ((JointCylinderGeneration.measurable_natural W hWm i (hs hk1)).sub
      (JointCylinderGeneration.measurable_natural W hWm i (hs (Nat.le_of_succ_le hk1)))).const_mul (v k i)

end LinearStochastic.JointDoleansMoments
