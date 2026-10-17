module

public import LinearStochastic.StaircaseControlClassification
public import Mathlib.Data.Nat.Find

@[expose] public section

/-! The first-return semantics of the exact orthogonal-elimination loop.
Every earlier state is live, so a zero residual returns a nonzero obstruction;
a zero retained width first occurs after a genuine update. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LinearStochastic.StaircaseFirstStop
open MeasureTheory ProbabilityTheory Module
open scoped NNReal
open Staircase StaircaseControlClassification PaperControlProperties

section General
variable {E U ι : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [Fintype ι]
  (s : AdjointCoefficients (𝕜:=ℝ) (E:=E) (U:=U) (ι:=ι))

/-- Either condition is literally checked by the loop, in the state before
its next update (zero width having already returned after the previous update). -/
def Stops (k : ℕ) : Prop :=
  (iterate s k).V.range=⊥ ∨ finrank ℝ (residual s (iterate s k).Q (iterate s k).V).range=0

/-- There is a first return within n updates. Before it all retained spaces
are nonzero and all residual ranks are positive. The failed branch is checked
at k<n; the successful branch occurs after 1,...,n updates. -/
theorem first_stop (hinit : s.flag 0≠⊥) : ∃ k≤finrank ℝ E,
    (∀ j<k, (iterate s j).V.range≠⊥ ∧ 0<finrank ℝ (residual s (iterate s j).Q (iterate s j).V).range) ∧
    (((iterate s k).V.range=⊥ ∧ 0<k) ∨
      (finrank ℝ (residual s (iterate s k).Q (iterate s k).V).range=0 ∧
        (iterate s k).V.range≠⊥ ∧ k<finrank ℝ E)) := by
  classical
  have hex : ∃ k, Stops s k := ⟨finrank ℝ E,Or.inr (iterate_residual_zero_at_dimension s)⟩
  let k := Nat.find hex
  have hk : k≤finrank ℝ E := Nat.find_min' hex (Or.inr (iterate_residual_zero_at_dimension s))
  have hs : Stops s k := Nat.find_spec hex
  have hprev : ∀ j<k, (iterate s j).V.range≠⊥ ∧ 0<finrank ℝ (residual s (iterate s j).Q (iterate s j).V).range := by
    intro j hj
    have hn := Nat.find_min hex hj
    exact ⟨fun hz=>hn (Or.inl hz),Nat.pos_of_ne_zero (fun hz=>hn (Or.inr hz))⟩
  refine ⟨k,hk,hprev,?_⟩
  by_cases hz : (iterate s k).V.range=⊥
  · left
    refine ⟨hz,Nat.pos_of_ne_zero ?_⟩
    intro h0
    rw [h0,iterate_range] at hz
    exact hinit hz
  · right
    refine ⟨hs.resolve_left hz,hz,?_⟩
    rcases stops_within_dimension s with ⟨j,hj,hjz⟩|hfinal
    · exact (Nat.find_min' hex (Or.inr hjz)).trans_lt hj
    · by_contra hkn
      have he : k=finrank ℝ E := le_antisymm hk (Nat.le_of_not_gt hkn)
      rw [he] at hz
      exact hz hfinal
end General

/-- The literal n-dimensional coefficient system has a first return with
exactly the loop's live-state invariant and n-update bound. Together with
`zero_residual_nonzero_none` and `zero_columns_success`, its two branches give
the actual stochastic output without assuming that a stopped state is reached. -/
theorem matrix_first_stop {n r m : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ) (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    let s := systemCoefficients A B C D
    ∃ k≤n,
      (∀ j<k, (iterate s j).V.range≠⊥ ∧ 0<finrank ℝ (residual s (iterate s j).Q (iterate s j).V).range) ∧
      (((iterate s k).V.range=⊥ ∧ 0<k) ∨
        (finrank ℝ (residual s (iterate s k).Q (iterate s k).V).range=0 ∧
          (iterate s k).V.range≠⊥ ∧ k<n)) := by
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let s := systemCoefficients A B C D
  have hinit : s.flag 0≠⊥ := by
    rw [s.flag_zero]
    exact top_ne_bot
  have hh := first_stop s hinit
  simpa only [finrank_euclideanSpace_fin] using hh

end LinearStochastic.StaircaseFirstStop
