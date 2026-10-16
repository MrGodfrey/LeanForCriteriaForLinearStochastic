import LinearStochastic.AlgebraStaircase

noncomputable section
namespace LinearStochastic.Staircase
open Module
open scoped BigOperators
variable {E U ι : Type}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [Fintype ι]
  (s : AdjointCoefficients (𝕜 := ℝ) (E := E) (U := U) (ι := ι))

/-- The exact stopping alternative for the n stages k=0,...,n−1 in the paper's pseudocode.
Either an actual residual has rank zero before n, or the final retained space is zero. -/
theorem stops_within_dimension :
    (∃ k < finrank ℝ E,
      finrank ℝ (residual s (iterate s k).Q (iterate s k).V).range = 0) ∨
      (iterate s (finrank ℝ E)).V.range = ⊥ := by
  classical
  by_cases h : ∃ k < finrank ℝ E, stepRank s k = 0
  · obtain ⟨k, hk, hz⟩ := h
    left
    refine ⟨k, hk, ?_⟩
    rw [iterate_residual_rank, ← stepRank_eq_prescribedDelta_increment, hz]
  · right
    have hlower : finrank ℝ E ≤ ∑ k ∈ Finset.range (finrank ℝ E), stepRank s k := by
      calc
        finrank ℝ E = ∑ k ∈ Finset.range (finrank ℝ E), (1 : ℕ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun k hk => Nat.one_le_iff_ne_zero.mpr
          (fun hz => h ⟨k, Finset.mem_range.mp hk, hz⟩)
    rw [sum_stepRank] at hlower
    have hdim := Submodule.finrank_le (s.flag (finrank ℝ E))
    have hz : finrank ℝ (s.flag (finrank ℝ E)) = 0 := by omega
    rw [iterate_range]
    exact Submodule.finrank_eq_zero.mp hz

#print axioms stops_within_dimension
end LinearStochastic.Staircase
