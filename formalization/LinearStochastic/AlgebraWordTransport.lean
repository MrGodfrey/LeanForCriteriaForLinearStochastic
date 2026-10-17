module

public import LinearStochastic.AlgebraWordMatrices

@[expose] public section

noncomputable section
namespace LinearStochastic.Words
section Transport
variable {𝕜 E F ι κ : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]

/-- Changing coordinates preserves the actual bounded word span. -/
theorem wordSpan_map (e : E ≃ₗ[𝕜] F)
    (M : ι → E →ₗ[𝕜] E) (N : ι → F →ₗ[𝕜] F)
    (h : ∀ i, (N i).comp e.toLinearMap = e.toLinearMap.comp (M i))
    (H : Submodule 𝕜 E) (k : ℕ) :
    (wordSpan M H k).map e.toLinearMap = wordSpan N (H.map e.toLinearMap) k := by
  simp only [← reach_eq_wordSpan]
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [reach_succ, step, Submodule.map_sup, Submodule.map_iSup, ih]
    congr 1
    apply iSup_congr
    intro i
    rw [← ih, ← Submodule.map_comp, ← Submodule.map_comp, h i]

/-- Reordering the generator family preserves every bounded word span. -/
theorem wordSpan_reindex (e : κ ≃ ι) (M : ι → E →ₗ[𝕜] E)
    (H : Submodule 𝕜 E) (k : ℕ) :
    wordSpan (fun i => M (e i)) H k = wordSpan M H k := by
  simp only [← reach_eq_wordSpan]
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [reach_succ, step, ih]
    rw [e.iSup_comp (g := fun i => (reach M H k).map (M i))]
end Transport
end LinearStochastic.Words

namespace LinearStochastic.WordMatrices
variable {n r q : ℕ}

/-- Ordinary matrix coordinates and the Euclidean Hilbert-space realization have the same span. -/
theorem wordSpan_euclidean_map (M : Fin q → Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin n) (Fin r) ℝ) (k : ℕ) :
    (Words.wordSpan (fun i => (M i).toEuclideanLin) H.toEuclideanLin.range k).map
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap =
      Words.wordSpan (fun i => (M i).mulVecLin) H.mulVecLin.range k := by
  have hr : H.toEuclideanLin.range.map
      (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap = H.mulVecLin.range := by
    ext y
    constructor
    · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
      exact ⟨u.ofLp, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨H.toEuclideanLin (WithLp.toLp 2 u), ⟨WithLp.toLp 2 u, rfl⟩, rfl⟩
  rw [Words.wordSpan_map (WithLp.linearEquiv 2 ℝ (Fin n → ℝ))
    (fun i => (M i).toEuclideanLin) (fun i => (M i).mulVecLin)
    (fun _ => rfl), hr]

/-- The rank of the displayed matrices tests fullness of the Euclidean word span too. -/
theorem cumulativeMatrix_full_rank_iff_euclidean
    (M : Fin q → Matrix (Fin n) (Fin n) ℝ)
    (H : Matrix (Fin n) (Fin r) ℝ) (k : ℕ) :
    (cumulativeMatrix M H k).rank = n ↔
      Words.wordSpan (fun i => (M i).toEuclideanLin) H.toEuclideanLin.range k = ⊤ := by
  rw [cumulativeMatrix_full_rank_iff, ← wordSpan_euclidean_map,
    Submodule.map_eq_top_iff]

#print axioms cumulativeMatrix_full_rank_iff_euclidean
end LinearStochastic.WordMatrices
