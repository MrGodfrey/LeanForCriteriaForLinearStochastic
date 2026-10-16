import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Separation of a linear range from an open convex cone

The theorem is proved from Mathlib's geometric Hahn–Banach theorem. No
closedness of the image of a closed semidefinite cone is asserted or used.
In fact, the argument works for any nonempty open convex set.
-/
namespace LinearStochastic.OpenConeAlternative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonempty open convex set disjoint from a linear subspace admits a
nonzero continuous functional positive on the set and zero on the subspace. -/
theorem separating_annihilator (L : Submodule ℝ E) (C : Set E)
    (hconv : Convex ℝ C) (hopen : IsOpen C) (hne : C.Nonempty)
    (hdisj : Disjoint C (L : Set E)) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ (∀ x ∈ L, f x = 0) ∧ ∀ x ∈ C, 0 < f x := by
  obtain ⟨f, a, hC, hL⟩ := geometric_hahn_banach_open hconv hopen L.convex hdisj
  have hz : ∀ x ∈ L, f x = 0 := by
    intro x hx
    by_contra hn
    have h := hL (((a - 1) / f x) • x) (L.smul_mem _ hx)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hn] at h
    linarith
  have ha : a ≤ 0 := by simpa using hL 0 L.zero_mem
  have hp : ∀ x ∈ C, 0 < (-f) x := by
    intro x hx
    have := hC x hx
    change 0 < -(f x)
    linarith
  refine ⟨-f, ?_, ?_, hp⟩
  · intro hzero
    obtain ⟨x, hx⟩ := hne
    have := hp x hx
    simpa [hzero] using this
  · intro x hx
    change -(f x) = 0
    rw [hz x hx, neg_zero]

/-- Strict feasibility or a separating certificate. The certificate is
constructed from failure of feasibility rather than added as an assumption. -/
theorem strict_feasibility_or_certificate (L : Submodule ℝ E) (C : Set E)
    (hconv : Convex ℝ C) (hopen : IsOpen C) (hne : C.Nonempty) :
    (∃ x, x ∈ L ∧ x ∈ C) ∨
    (∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧ (∀ x ∈ L, f x = 0) ∧ ∀ x ∈ C, 0 < f x) := by
  classical
  by_cases h : ∃ x, x ∈ L ∧ x ∈ C
  · exact Or.inl h
  · apply Or.inr
    apply separating_annihilator L C hconv hopen hne
    rw [Set.disjoint_left]
    intro x hxC hxL
    exact h ⟨x, hxL, hxC⟩

end LinearStochastic.OpenConeAlternative
