import LinearStochastic.AlgebraFlag

/-!
# Rank difference for an existential linear constraint

This module proves the finite-dimensional elimination identity used in paper
Theorem `thm:rank`. The maps `K` and `N` are arbitrary and no rank formula is
assumed. Matrix/block construction is separate.
-/
namespace LinearStochastic
open Module

variable {𝕜 E F G : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [AddCommGroup G] [Module 𝕜 G]

/-- The existential solution space `{v | ∃ a, K v + N a = 0}`. -/
def feasibleSpace (K : E →ₗ[𝕜] G) (N : F →ₗ[𝕜] G) : Submodule 𝕜 E :=
  N.range.comap K

theorem mem_feasibleSpace (K : E →ₗ[𝕜] G) (N : F →ₗ[𝕜] G) (v : E) :
    v ∈ feasibleSpace K N ↔ ∃ a, K v + N a = 0 := by
  change (∃ a, N a = K v) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨-a, by simp [ha]⟩
  · rintro ⟨a, ha⟩
    refine ⟨-a, ?_⟩
    simp only [map_neg]
    exact (eq_neg_of_add_eq_zero_left ha).symm

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- Exact rank-codimension identity, valid for every linear pair. -/
theorem rank_difference_eq_codimension (K : E →ₗ[𝕜] G) (N : F →ₗ[𝕜] G) :
    finrank 𝕜 (N.coprod K).range - finrank 𝕜 N.range =
      finrank 𝕜 E - finrank 𝕜 (feasibleSpace K N) := by
  let T := N.coprod K
  let P := T.ker
  let p : P →ₗ[𝕜] E := (LinearMap.snd 𝕜 F E).comp P.subtype
  have hr : p.range = feasibleSpace K N := by
    ext v
    constructor
    · rintro ⟨⟨⟨a, x⟩, hx⟩, rfl⟩
      rw [mem_feasibleSpace]
      refine ⟨a, ?_⟩
      change N a + K x = 0 at hx
      change K x + N a = 0
      rwa [add_comm]
    · intro hv
      obtain ⟨a, ha⟩ := (mem_feasibleSpace K N v).mp hv
      refine ⟨⟨(a, v), ?_⟩, rfl⟩
      change N a + K v = 0
      rwa [add_comm]
  let e : p.ker ≃ₗ[𝕜] N.ker :=
    { toFun := fun x => ⟨x.val.val.1, by
        have h1 := x.val.property
        have h2 := x.property
        change N x.val.val.1 + K x.val.val.2 = 0 at h1
        change x.val.val.2 = 0 at h2
        simpa [h2] using h1⟩
      invFun := fun a => ⟨⟨(a.val, 0), by
        change N a.val + K 0 = 0
        simp⟩, by rfl⟩
      left_inv := by
        intro x
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact x.property.symm
      right_inv := by intro a; rfl
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hT := T.finrank_range_add_finrank_ker
  have hp := p.finrank_range_add_finrank_ker
  have hN := N.finrank_range_add_finrank_ker
  have he := e.finrank_eq
  rw [hr, he] at hp
  rw [Module.finrank_prod] at hT
  change finrank 𝕜 (N.coprod K).range + finrank 𝕜 P = finrank 𝕜 F + finrank 𝕜 E at hT
  change finrank 𝕜 (feasibleSpace K N) + finrank 𝕜 N.ker = finrank 𝕜 P at hp
  omega

#print axioms rank_difference_eq_codimension
end LinearStochastic
