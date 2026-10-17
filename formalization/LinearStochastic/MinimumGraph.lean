module

public import LinearStochastic.MinimumContinuity
public import LinearStochastic.SemialgebraicCoordinates

@[expose] public section

noncomputable section
namespace LinearStochastic.ParametricMinimum
open QuadraticMinimum
variable {X E F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Exact first-order characterization of an attained quadratic minimum:
a feasible point has this value and no feasible point has a smaller value. -/
theorem value_eq_iff (R : X → E × F → Prop)
    (hc : IsClosed {p : X × (E × F) | R p.1 p.2})
    (hne : ∀ x, ∃ z, R x z) (x : X) (s : ℝ) :
    s = value R hc hne x ↔ ∃ z, R x z ∧ objective z = s ∧
      ¬∃ w, R x w ∧ objective w < s := by
  constructor
  · intro hs
    refine ⟨minimizer R hc hne x,(minimizer_spec R hc hne x).1,hs.symm,?_⟩
    rintro ⟨w,hw,hwlt⟩
    exact (not_lt_of_ge (value_le R hc hne x w hw)) (by rwa [←hs])
  · rintro ⟨z,hz,hzs,hmin⟩
    apply le_antisymm
    · by_contra h
      exact hmin ⟨minimizer R hc hne x,(minimizer_spec R hc hne x).1,lt_of_not_ge h⟩
    · simpa only [hzs] using value_le R hc hne x z hz

end LinearStochastic.ParametricMinimum

namespace LinearStochastic.MatrixValue
open scoped Matrix.Norms.Frobenius
open MatrixNormalization QuadraticMinimum
variable {n r m : ℕ}
variable (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hfeas : ∀ ρ : Set.Ici (1 : ℝ), ∃ P K, Feasible A B C D ρ P K)

theorem value_eq_iff (ρ : Set.Ici (1 : ℝ)) (s : ℝ) :
    s = value A B C D hfeas ρ ↔ ∃ P K, Feasible A B C D ρ P K ∧
      matrixObjective (P,K) = s ∧ ¬∃ P' K', Feasible A B C D ρ P' K' ∧
        matrixObjective (P',K') < s := by
  have h := ParametricMinimum.value_eq_iff
    (fun (ρ : Set.Ici (1 : ℝ)) (z : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin r) (Fin n) ℝ) =>
      Feasible A B C D ρ.val z.1 z.2)
    (closed_ray_graph A B C D) (fun ρ => let ⟨P,K,h⟩ := hfeas ρ; ⟨(P,K),h⟩) ρ s
  simpa only [value,Prod.exists,QuadraticMinimum.matrixObjective] using h

/-- An ambient-real extension used only to state the graph on [1,∞). -/
def valueReal (ρ : ℝ) : ℝ := if h : 1 ≤ ρ then value A B C D hfeas ⟨ρ,h⟩ else 0

theorem valueReal_on_ray (ρ : ℝ) (hρ : 1 ≤ ρ) :
    valueReal A B C D hfeas ρ = value A B C D hfeas ⟨ρ,hρ⟩ := dif_pos hρ

theorem valueReal_continuousOn : ContinuousOn (valueReal A B C D hfeas) (Set.Ici 1) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert continuous_value A B C D hfeas using 1
  ext ρ
  exact valueReal_on_ray A B C D hfeas ρ ρ.property

/-- The actual minimum graph is exactly the manuscript's polynomial-quantifier
formula; neither semialgebraicity nor elimination is assumed here. -/
theorem rayGraph_iff (v : Fin 2 → ℝ) :
    v ∈ SemialgebraicCoordinates.rayGraph (valueReal A B C D hfeas) ↔
      1 ≤ v 0 ∧ ∃ P K, Feasible A B C D (v 0) P K ∧ matrixObjective (P,K) = v 1 ∧
        ¬∃ P' K', Feasible A B C D (v 0) P' K' ∧ matrixObjective (P',K') < v 1 := by
  constructor
  · rintro ⟨hρ,hs⟩
    refine ⟨hρ,?_⟩
    apply (value_eq_iff A B C D hfeas ⟨v 0,hρ⟩ (v 1)).mp
    rwa [valueReal_on_ray A B C D hfeas _ hρ] at hs
  · rintro ⟨hρ,hs⟩
    refine ⟨hρ,?_⟩
    rw [valueReal_on_ray A B C D hfeas _ hρ]
    exact (value_eq_iff A B C D hfeas ⟨v 0,hρ⟩ (v 1)).mpr hs

end LinearStochastic.MatrixValue
