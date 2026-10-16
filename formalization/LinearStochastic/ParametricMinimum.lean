import LinearStochastic.MatrixMinimum
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Maps.Proper.Basic

noncomputable section
namespace LinearStochastic.ParametricMinimum
open Set QuadraticMinimum
variable {X E F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

variable (R : X → E × F → Prop)
  (hc : IsClosed {p : X × (E × F) | R p.1 p.2})
  (hne : ∀ x, ∃ z, R x z)

include hc hne

theorem exists_minimum (x : X) :
    ∃ z, R x z ∧ ∀ w, R x w → objective z ≤ objective w := by
  exact QuadraticMinimum.exists_minimum {z | R x z}
    (hc.preimage (continuous_const.prodMk continuous_id)) (hne x)

/-- A selected actual minimizer, whose existence has already been proved. -/
def minimizer (x : X) : E × F := (exists_minimum R hc hne x).choose

theorem minimizer_spec (x : X) :
    R x (minimizer R hc hne x) ∧
      ∀ w, R x w → objective (minimizer R hc hne x) ≤ objective w :=
  (exists_minimum R hc hne x).choose_spec

def value (x : X) : ℝ := objective (minimizer R hc hne x)

theorem value_nonneg (x : X) : 0 ≤ value R hc hne x := objective_nonneg _

theorem value_le (x : X) (z : E × F) (hz : R x z) :
    value R hc hne x ≤ objective z := (minimizer_spec R hc hne x).2 z hz

/-- Closed bounded projections give closed value sublevel sets. The compact
bound is derived from the squared-norm objective, including negative levels. -/
theorem isClosed_sublevel (c : ℝ) : IsClosed {x | value R hc hne x ≤ c} := by
  let K : Set (E × F) := Metric.closedBall 0 (c+1)
  have hK : IsCompact K := isCompact_closedBall 0 (c+1)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let S : Set (X × K) := {p | R p.1 p.2.val ∧ objective p.2.val ≤ c}
  have hS : IsClosed S :=
    (hc.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).inter
      (isClosed_le (objective_continuous.comp (continuous_subtype_val.comp continuous_snd))
        continuous_const)
  have he : Prod.fst '' S = {x | value R hc hne x ≤ c} := by
    ext x
    constructor
    · rintro ⟨⟨y,z⟩,⟨hz,hzc⟩,rfl⟩
      exact (value_le R hc hne y z.val hz).trans hzc
    · intro hx
      let z := minimizer R hc hne x
      have hz : z ∈ K := by
        change z ∈ Metric.closedBall (0 : E × F) (c+1)
        rw [Metric.mem_closedBall,dist_zero_right]
        have hv : objective z ≤ c := hx
        linarith [norm_le_objective_add_one z]
      exact ⟨(x,⟨z,hz⟩),⟨(minimizer_spec R hc hne x).1,hx⟩,rfl⟩
  rw [← he]
  exact isClosedMap_fst_of_compactSpace S hS

theorem lowerSemicontinuous_value : LowerSemicontinuous (value R hc hne) := by
  apply lowerSemicontinuous_iff_isClosed_preimage.mpr
  exact isClosed_sublevel R hc hne

end LinearStochastic.ParametricMinimum

namespace LinearStochastic.MatrixValue
open scoped Matrix.Norms.Frobenius
open MatrixNormalization MatrixMinimum ParametricMinimum
variable {n r m : ℕ}
variable (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ)
    (hfeas : ∀ ρ : Set.Ici (1 : ℝ), ∃ P K, Feasible A B C D ρ P K)

theorem closed_ray_graph : IsClosed {p : Set.Ici (1 : ℝ) ×
    (Matrix (Fin n) (Fin n) ℝ × Matrix (Fin r) (Fin n) ℝ) |
      Feasible A B C D p.1.val p.2.1 p.2.2} :=
  (isClosed_feasible_graph A B C D).preimage
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

def value (ρ : Set.Ici (1 : ℝ)) : ℝ :=
  ParametricMinimum.value (fun (ρ : Set.Ici (1 : ℝ)) (z : Matrix (Fin n) (Fin n) ℝ × Matrix (Fin r) (Fin n) ℝ) => Feasible A B C D ρ.val z.1 z.2)
    (closed_ray_graph A B C D)
    (fun ρ => let ⟨P,K,h⟩ := hfeas ρ; ⟨(P,K),h⟩) ρ

/-- The manuscript's actual Frobenius minimum is lower semicontinuous on [1,∞).
The proof uses the closed parameterized LMI and actual coercive minima. -/
theorem lowerSemicontinuous_value : LowerSemicontinuous (value A B C D hfeas) :=
  ParametricMinimum.lowerSemicontinuous_value _ _ _

#print axioms lowerSemicontinuous_value
end LinearStochastic.MatrixValue
