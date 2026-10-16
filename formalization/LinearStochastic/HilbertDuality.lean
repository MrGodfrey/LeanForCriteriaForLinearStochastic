import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
The Hilbert-space fact used at the beginning of `lem:approximate`.
This theorem is genuinely infinite-dimensional. It does not identify an
SDE terminal map's adjoint with the BSDE observation; that stochastic
duality identity remains to be proved separately.
-/

namespace LinearStochastic.HilbertDuality

variable {U Y : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

theorem dense_range_iff_adjoint_ker_eq_bot (M : U →L[ℝ] Y) :
    (LinearMap.range M.toLinearMap).topologicalClosure = ⊤ ↔
      LinearMap.ker (ContinuousLinearMap.adjoint M).toLinearMap = ⊥ := by
  rw [Submodule.topologicalClosure_eq_top_iff, M.orthogonal_range]

end LinearStochastic.HilbertDuality
