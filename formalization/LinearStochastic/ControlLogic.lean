import Mathlib

/-!
Algebraic consequences of a linear terminal map.

Paper: Definition `def:control` and Remark `rem:terminal-interpretation`.
`X` is the initial-state space, `U` the admissible-control space, and `Y`
the terminal-state space. They are intentionally distinct. This file does
NOT construct the stochastic spaces or prove that an SDE has this terminal
map. Instantiating these definitions with the paper's Brownian L² spaces
is a separate, currently unproved obligation.
-/

namespace LinearStochastic.ControlLogic

variable {X U Y : Type*}
  [AddCommGroup X] [Module ℝ X]
  [AddCommGroup U] [Module ℝ U]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def terminal (Φ : X →ₗ[ℝ] Y) (Ψ : U →ₗ[ℝ] Y) (x : X) (u : U) : Y :=
  Φ x + Ψ u

def Exact (Φ : X →ₗ[ℝ] Y) (Ψ : U →ₗ[ℝ] Y) : Prop :=
  ∀ x ξ, ∃ u, terminal Φ Ψ x u = ξ

def ExactNull (Φ : X →ₗ[ℝ] Y) (Ψ : U →ₗ[ℝ] Y) : Prop :=
  ∀ x, ∃ u, terminal Φ Ψ x u = 0

def ExactTerminal (Φ : X →ₗ[ℝ] Y) (Ψ : U →ₗ[ℝ] Y) : Prop :=
  ∀ ξ, ∃ x u, terminal Φ Ψ x u = ξ

def Approximate (Φ : X →ₗ[ℝ] Y) (Ψ : U →ₗ[ℝ] Y) : Prop :=
  ∀ x ξ ε, 0 < ε → ∃ u, ‖terminal Φ Ψ x u - ξ‖ ^ 2 < ε

def ApproximateNull (Φ : X →ₗ[ℝ] Y) (Ψ : U →ₗ[ℝ] Y) : Prop :=
  ∀ x ε, 0 < ε → ∃ u, ‖terminal Φ Ψ x u‖ ^ 2 < ε

theorem exact_iff_surjective (Φ : X →ₗ[ℝ] Y) (Ψ : U →ₗ[ℝ] Y) :
    Exact Φ Ψ ↔ Function.Surjective Ψ := by
  constructor
  · intro h ξ
    obtain ⟨u, hu⟩ := h 0 ξ
    exact ⟨u, by simpa [terminal] using hu⟩
  · intro h x ξ
    obtain ⟨u, hu⟩ := h (ξ - Φ x)
    exact ⟨u, by simp [terminal, hu]⟩

theorem exact_implies_approximate (Φ : X →ₗ[ℝ] Y) (Ψ : U →ₗ[ℝ] Y)
    (h : Exact Φ Ψ) : Approximate Φ Ψ := by
  intro x ξ ε hε
  obtain ⟨u, hu⟩ := h x ξ
  exact ⟨u, by simpa [hu] using hε⟩

theorem exact_implies_exactNull (Φ : X →ₗ[ℝ] Y) (Ψ : U →ₗ[ℝ] Y)
    (h : Exact Φ Ψ) : ExactNull Φ Ψ := fun x => h x 0

theorem exactNull_implies_approximateNull (Φ : X →ₗ[ℝ] Y) (Ψ : U →ₗ[ℝ] Y)
    (h : ExactNull Φ Ψ) : ApproximateNull Φ Ψ := by
  intro x ε hε
  obtain ⟨u, hu⟩ := h x
  exact ⟨u, by simpa [hu] using hε⟩

theorem approximate_implies_approximateNull (Φ : X →ₗ[ℝ] Y) (Ψ : U →ₗ[ℝ] Y)
    (h : Approximate Φ Ψ) : ApproximateNull Φ Ψ := by
  intro x ε hε
  simpa using h x 0 ε hε

theorem exact_iff_terminal_and_null (Φ : X →ₗ[ℝ] Y) (Ψ : U →ₗ[ℝ] Y) :
    Exact Φ Ψ ↔ ExactTerminal Φ Ψ ∧ ExactNull Φ Ψ := by
  constructor
  · intro h
    exact ⟨fun ξ => ⟨0, h 0 ξ⟩, exact_implies_exactNull Φ Ψ h⟩
  · rintro ⟨hterminal, hnull⟩ x ξ
    obtain ⟨xξ, uξ, hξ⟩ := hterminal ξ
    obtain ⟨u0, h0⟩ := hnull (x - xξ)
    refine ⟨uξ + u0, ?_⟩
    dsimp [terminal] at hξ h0 ⊢
    rw [map_sub] at h0
    rw [map_add]
    calc
      Φ x + (Ψ uξ + Ψ u0) = (Φ xξ + Ψ uξ) + (Φ x - Φ xξ + Ψ u0) := by abel
      _ = ξ := by rw [hξ, h0, add_zero]

end LinearStochastic.ControlLogic
