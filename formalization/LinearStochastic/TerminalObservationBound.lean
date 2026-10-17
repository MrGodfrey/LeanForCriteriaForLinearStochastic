module

public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-! The actual open-mapping step in exact controllability. The pairing is
explicit so the application must establish the real SDE/adjoint identity;
no lower bound or bounded preimage oracle is assumed. -/
noncomputable section
namespace LinearStochastic.TerminalObservationBound
open Filter
open scoped Topology InnerProductSpace
variable {U Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- Actual surjectivity of a continuous linear map forces a uniform lower
bound for every vector satisfying its genuine dual pairing identity. -/
theorem observation_bound (M : U →L[ℝ] Y) (hs : Function.Surjective M) :
    ∃ K : ℝ, 0 < K ∧ ∀ (η : Y) (z : U),
      (∀ u, inner ℝ (M u) η = inner ℝ u z) → ‖η‖ ≤ K*‖z‖ := by
  obtain ⟨K,hK,hpre⟩ := M.exists_preimage_norm_le hs
  refine ⟨K,hK,?_⟩
  intro η z hd
  obtain ⟨u,hu,hun⟩ := hpre η
  have hh : ‖η‖^2 ≤ (K*‖η‖)*‖z‖ := by
    calc
      _ = inner ℝ η η := (real_inner_self_eq_norm_sq η).symm
      _ = inner ℝ (M u) η := by rw [hu]
      _ = inner ℝ u z := hd u
      _ ≤ ‖u‖*‖z‖ := real_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hun (norm_nonneg _)
  by_cases hz : ‖η‖ = 0
  · rw [hz]
    exact mul_nonneg hK.le (norm_nonneg _)
  · have hp : 0 < ‖η‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

/-- A genuinely constructed unit-size terminal sequence with vanishing
observations contradicts surjectivity. All stochastic inputs stay explicit. -/
theorem not_surjective_of_vanishing_observations (M : U →L[ℝ] Y)
    (η : ℕ → Y) (z : ℕ → U)
    (hd : ∀ n u, inner ℝ (M u) (η n) = inner ℝ u (z n))
    (hη : Tendsto (fun n ↦ ‖η n‖) atTop (𝓝 1))
    (hz : Tendsto (fun n ↦ ‖z n‖) atTop (𝓝 0)) : ¬Function.Surjective M := by
  intro hs
  obtain ⟨K,_,hK⟩ := observation_bound M hs
  have hlim : Tendsto (fun n ↦ K*‖z n‖) atTop (𝓝 0) := by simpa using hz.const_mul K
  have hbad : (1:ℝ) ≤ 0 := le_of_tendsto_of_tendsto' hη hlim (fun n ↦ hK (η n) (z n) (hd n))
  norm_num at hbad

end LinearStochastic.TerminalObservationBound
