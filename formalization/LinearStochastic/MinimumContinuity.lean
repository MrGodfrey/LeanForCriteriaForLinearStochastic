module

public import LinearStochastic.ParametricMinimum
public import LinearStochastic.LMIStability
public import Mathlib.Topology.Order.LeftRight

@[expose] public section

noncomputable section
namespace LinearStochastic.ParametricMinimum
open Set QuadraticMinimum
variable {X E F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem objective_smul (c : ℝ) (z : E × F) : objective (c•z) = c^2*objective z := by
  simp only [objective,Prod.smul_fst,Prod.smul_snd,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs]
  ring

/-- Strict dilations which remain locally feasible imply upper semicontinuity
of the actual, attained minimum. This will be discharged for the literal LMI. -/
theorem upperSemicontinuous_value
    (R : X → E × F → Prop) (hc : IsClosed {p : X × (E × F) | R p.1 p.2})
    (hne : ∀ x, ∃ z, R x z)
    (hstable : ∀ x z, R x z → ∀ c : ℝ, 1 < c → ∀ᶠ y in nhds x, R y (c•z)) :
    UpperSemicontinuous (value R hc hne) := by
  intro x a ha
  let z := minimizer R hc hne x
  have hnear : ∀ᶠ c : ℝ in nhds 1, c^2*objective z < a := by
    have hcont : Continuous (fun c : ℝ => c^2*objective z) :=
      (continuous_id.pow 2).mul continuous_const
    have ha' : objective z < a := ha
    exact hcont.continuousAt.eventually_lt_const (by simpa only [one_pow,one_mul] using ha')
  obtain ⟨c,hc1,hca⟩ := ((frequently_gt_nhds (1 : ℝ)).and_eventually hnear).exists
  filter_upwards [hstable x z (minimizer_spec R hc hne x).1 c hc1] with y hy
  have hmin := value_le R hc hne y (c•z) hy
  rw [objective_smul] at hmin
  exact hmin.trans_lt hca

theorem continuous_value
    (R : X → E × F → Prop) (hc : IsClosed {p : X × (E × F) | R p.1 p.2})
    (hne : ∀ x, ∃ z, R x z)
    (hstable : ∀ x z, R x z → ∀ c : ℝ, 1 < c → ∀ᶠ y in nhds x, R y (c•z)) :
    Continuous (value R hc hne) :=
  continuous_iff_lower_upperSemicontinuous.mpr
    ⟨lowerSemicontinuous_value R hc hne,upperSemicontinuous_value R hc hne hstable⟩

end LinearStochastic.ParametricMinimum

namespace LinearStochastic.MatrixValue
open scoped Matrix.Norms.Frobenius
open MatrixNormalization MatrixMinimum ParametricMinimum
variable {n r m : ℕ}
variable (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hfeas : ∀ ρ : Set.Ici (1 : ℝ), ∃ P K, Feasible A B C D ρ P K)

/-- Continuity of the manuscript's attained Frobenius minimum on the entire
closed ray [1,∞), derived from the original normalized LMI. -/
theorem continuous_value : Continuous (value A B C D hfeas) := by
  apply ParametricMinimum.continuous_value
  intro ρ z hz c hc
  have h := MatrixStability.scaled_feasible_near A B C D ρ z.1 z.2 hz c hc
  exact continuous_subtype_val.continuousAt.eventually h

#print axioms continuous_value
end LinearStochastic.MatrixValue
