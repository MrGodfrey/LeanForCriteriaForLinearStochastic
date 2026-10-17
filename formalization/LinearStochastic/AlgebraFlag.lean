module

public import Mathlib

@[expose] public section

/-!
# The algebraic obstruction flag (paper Lemma `lem:flag`)

The maps `A`, `B`, `C i`, `D i` represent the *transposed* coefficient
matrices in (eq:map). This works over any field and finite family of channels.
No stochastic theorem or controllability claim is assumed.
-/
namespace LinearStochastic
open Module
open scoped BigOperators
variable {𝕜 E U ι : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup U] [Module 𝕜 U] [Fintype ι]

structure AdjointCoefficients where
  A : E →ₗ[𝕜] E
  B : E →ₗ[𝕜] U
  C : ι → E →ₗ[𝕜] E
  D : ι → E →ₗ[𝕜] U

namespace AdjointCoefficients
variable (s : AdjointCoefficients (𝕜 := 𝕜) (E := E) (U := U) (ι := ι))

/-- Exactly the existential conditions in manuscript (eq:map). -/
def obstruction (V : Submodule 𝕜 E) : Submodule 𝕜 E where
  carrier := {v | v ∈ V ∧ ∃ w : ι → E,
    (∀ i, w i ∈ V) ∧ s.B v + ∑ i, s.D i (w i) = 0 ∧
    s.A v + ∑ i, s.C i (w i) ∈ V}
  zero_mem' := by
    refine ⟨V.zero_mem, fun _ => 0, ?_, ?_, ?_⟩ <;> simp
  add_mem' := by
    rintro v v' ⟨hv, w, hw, hB, hA⟩ ⟨hv', w', hw', hB', hA'⟩
    refine ⟨V.add_mem hv hv', fun i => w i + w' i,
      fun i => V.add_mem (hw i) (hw' i), ?_, ?_⟩
    · simpa only [map_add, Finset.sum_add_distrib, add_add_add_comm, add_zero] using congrArg₂ (· + ·) hB hB'
    · simpa only [map_add, Finset.sum_add_distrib, add_add_add_comm] using V.add_mem hA hA'
  smul_mem' := by
    rintro a v ⟨hv, w, hw, hB, hA⟩
    refine ⟨V.smul_mem a hv, fun i => a • w i,
      fun i => V.smul_mem a (hw i), ?_, ?_⟩
    · simp only [map_smul, ← Finset.smul_sum, ← smul_add, hB, smul_zero]
    · simpa only [map_smul, ← Finset.smul_sum, ← smul_add] using V.smul_mem a hA

@[simp] theorem mem_obstruction (V : Submodule 𝕜 E) (v : E) :
    v ∈ s.obstruction V ↔ v ∈ V ∧ ∃ w : ι → E,
      (∀ i, w i ∈ V) ∧ s.B v + ∑ i, s.D i (w i) = 0 ∧
      s.A v + ∑ i, s.C i (w i) ∈ V := Iff.rfl

theorem obstruction_le (V : Submodule 𝕜 E) : s.obstruction V ≤ V := fun _ h => h.1

theorem obstruction_mono : Monotone s.obstruction := by
  intro V W h v hv
  obtain ⟨hv, w, hw, hB, hA⟩ := hv
  exact ⟨h hv, w, fun i => h (hw i), hB, h hA⟩

/-- V₀ = E, Vₖ₊₁ = R(Vₖ), with no truncation built into the definition. -/
def flag (k : ℕ) : Submodule 𝕜 E := Nat.rec ⊤ (fun _ V => s.obstruction V) k

@[simp] theorem flag_zero : s.flag 0 = ⊤ := rfl
@[simp] theorem flag_succ (k : ℕ) : s.flag (k + 1) = s.obstruction (s.flag k) := rfl

theorem flag_step_le (k : ℕ) : s.flag (k + 1) ≤ s.flag k := s.obstruction_le _
theorem flag_antitone : Antitone s.flag := antitone_nat_of_succ_le s.flag_step_le

theorem stationary_of_step_eq {k : ℕ} (h : s.flag (k + 1) = s.flag k) :
    ∀ l, s.flag (k + l) = s.flag k := by
  intro l
  induction l with
  | zero => simp
  | succ l ih =>
    rw [show k + (l + 1) = (k + l) + 1 by omega, s.flag_succ, ih, ← s.flag_succ, h]

/-- The full relation, retaining witnesses rather than projecting them away. -/
def witnessSpace (V : Submodule 𝕜 E) : Submodule 𝕜 (E × (ι → E)) where
  carrier := {p | p.1 ∈ V ∧ (∀ i, p.2 i ∈ V) ∧
    s.B p.1 + ∑ i, s.D i (p.2 i) = 0 ∧ s.A p.1 + ∑ i, s.C i (p.2 i) ∈ V}
  zero_mem' := by simp
  add_mem' := by
    rintro ⟨v, w⟩ ⟨v', w'⟩ ⟨hv, hw, hB, hA⟩ ⟨hv', hw', hB', hA'⟩
    refine ⟨V.add_mem hv hv', fun i => V.add_mem (hw i) (hw' i), ?_, ?_⟩
    · change s.B (v + v') + ∑ i, s.D i (w i + w' i) = 0
      simpa only [map_add, Finset.sum_add_distrib, add_add_add_comm, add_zero]
        using congrArg₂ (· + ·) hB hB'
    · change s.A (v + v') + ∑ i, s.C i (w i + w' i) ∈ V
      simpa only [map_add, Finset.sum_add_distrib, add_add_add_comm] using V.add_mem hA hA'
  smul_mem' := by
    rintro a ⟨v, w⟩ ⟨hv, hw, hB, hA⟩
    refine ⟨V.smul_mem a hv, fun i => V.smul_mem a (hw i), ?_, ?_⟩
    · change s.B (a • v) + ∑ i, s.D i (a • w i) = 0
      simp only [map_smul, ← Finset.smul_sum, ← smul_add, hB, smul_zero]
    · change s.A (a • v) + ∑ i, s.C i (a • w i) ∈ V
      simpa only [map_smul, ← Finset.smul_sum, ← smul_add] using V.smul_mem a hA

/-- The manuscript's invariance property, including global linear selectors. -/
def HasInvariantSelectors (V : Submodule 𝕜 E) : Prop :=
  ∃ Γ : ι → E →ₗ[𝕜] E, ∀ v ∈ V,
    (∀ i, Γ i v ∈ V) ∧
    s.B v + ∑ i, s.D i (Γ i v) = 0 ∧
    s.A v + ∑ i, s.C i (Γ i v) ∈ V

/-- Linear selectors are constructed from feasibility, not assumed. -/
theorem selectors_of_fixed {V : Submodule 𝕜 E} (h : V ≤ s.obstruction V) :
    s.HasInvariantSelectors V := by
  classical
  let P := s.witnessSpace V
  let π : P →ₗ[𝕜] V :=
    ((LinearMap.fst 𝕜 E (ι → E)).comp P.subtype).codRestrict V (fun p => p.property.1)
  have hπ : Function.Surjective π := by
    intro v
    obtain ⟨_, w, hw, hB, hA⟩ := h v.property
    exact ⟨⟨(v, w), v.property, hw, hB, hA⟩, rfl⟩
  obtain ⟨g, hg⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  obtain ⟨g', hg'⟩ := g.exists_extend
  let Γ : ι → E →ₗ[𝕜] E := fun i =>
    (LinearMap.proj i).comp ((LinearMap.snd 𝕜 E (ι → E)).comp (P.subtype.comp g'))
  refine ⟨Γ, ?_⟩
  intro v hv
  have hext : g' v = g ⟨v, hv⟩ := LinearMap.congr_fun hg' ⟨v, hv⟩
  have hfirst : ((g' v).val).1 = v := by
    have ht := congrArg Subtype.val (LinearMap.congr_fun hg ⟨v, hv⟩)
    change ((g ⟨v, hv⟩).val).1 = v at ht
    rw [hext]
    exact ht
  have hp := (g' v).property
  change ((g' v).val).1 ∈ V ∧
    (∀ i, ((g' v).val).2 i ∈ V) ∧
    s.B ((g' v).val).1 + ∑ i, s.D i (((g' v).val).2 i) = 0 ∧
    s.A ((g' v).val).1 + ∑ i, s.C i (((g' v).val).2 i) ∈ V at hp
  change (∀ i, ((g' v).val).2 i ∈ V) ∧
    s.B v + ∑ i, s.D i (((g' v).val).2 i) = 0 ∧
    s.A v + ∑ i, s.C i (((g' v).val).2 i) ∈ V
  rw [hfirst] at hp
  exact hp.2

theorem fixed_of_selectors {V : Submodule 𝕜 E} (h : s.HasInvariantSelectors V) :
    V ≤ s.obstruction V := by
  obtain ⟨Γ, hΓ⟩ := h
  intro v hv
  exact ⟨hv, fun i => Γ i v, hΓ v hv⟩

theorem fixed_iff_selectors (V : Submodule 𝕜 E) :
    s.obstruction V = V ↔ s.HasInvariantSelectors V := by
  constructor
  · intro h; exact s.selectors_of_fixed h.ge
  · intro h; exact le_antisymm (s.obstruction_le V) (s.fixed_of_selectors h)

variable [FiniteDimensional 𝕜 E]

/-- Finite-dimensional stationarity, with the manuscript's explicit bound n. -/
theorem flag_stable_at_finrank :
    s.flag (finrank 𝕜 E + 1) = s.flag (finrank 𝕜 E) := by
  by_contra hn
  have strict (k : ℕ) (hk : k ≤ finrank 𝕜 E) : s.flag (k + 1) < s.flag k := by
    refine lt_of_le_of_ne (s.flag_step_le k) ?_
    intro heq
    have h1 := s.stationary_of_step_eq heq (finrank 𝕜 E - k)
    have h2 := s.stationary_of_step_eq heq (finrank 𝕜 E + 1 - k)
    have hk1 : k + (finrank 𝕜 E - k) = finrank 𝕜 E := by omega
    have hk2 : k + (finrank 𝕜 E + 1 - k) = finrank 𝕜 E + 1 := by omega
    rw [hk1] at h1
    rw [hk2] at h2
    exact hn (h2.trans h1.symm)
  have bound : ∀ k, k ≤ finrank 𝕜 E + 1 → finrank 𝕜 (s.flag k) + k ≤ finrank 𝕜 E := by
    intro k
    induction k with
    | zero => intro _; simpa only [Nat.add_zero] using (s.flag 0).finrank_le
    | succ k ih =>
      intro hk
      have hi := ih (by omega)
      have hd := Submodule.finrank_lt_finrank_of_lt (strict k (by omega))
      omega
  have := bound (finrank 𝕜 E + 1) (by omega)
  omega

theorem flag_stationary (l : ℕ) :
    s.flag (finrank 𝕜 E + l) = s.flag (finrank 𝕜 E) :=
  s.stationary_of_step_eq s.flag_stable_at_finrank l

omit [FiniteDimensional 𝕜 E] in
/-- Pointwise feasibility is enough for maximality; no linear selector is assumed here. -/
theorem fixed_le_flag {V : Submodule 𝕜 E} (h : V ≤ s.obstruction V) (k : ℕ) :
    V ≤ s.flag k := by
  induction k with
  | zero => exact le_top
  | succ k ih => exact h.trans (s.obstruction_mono ih)

/-- The stabilized flag is the greatest fixed point of the actual obstruction operator. -/
theorem flag_greatest_fixed_point :
    s.obstruction (s.flag (finrank 𝕜 E)) = s.flag (finrank 𝕜 E) ∧
    ∀ V, s.obstruction V = V → V ≤ s.flag (finrank 𝕜 E) := by
  refine ⟨s.flag_stable_at_finrank, ?_⟩
  intro V h
  exact s.fixed_le_flag h.ge _

/-- Full algebraic statement of paper Lemma `lem:flag`. -/
theorem flag_lemma :
    Antitone s.flag ∧
    (∀ l, s.flag (finrank 𝕜 E + l) = s.flag (finrank 𝕜 E)) ∧
    s.HasInvariantSelectors (s.flag (finrank 𝕜 E)) ∧
    (∀ V, s.HasInvariantSelectors V → V ≤ s.flag (finrank 𝕜 E)) := by
  refine ⟨s.flag_antitone, s.flag_stationary, ?_, ?_⟩
  · exact s.selectors_of_fixed s.flag_stable_at_finrank.ge
  · intro V h; exact s.fixed_le_flag (s.fixed_of_selectors h) _

#print axioms flag_lemma

end AdjointCoefficients
end LinearStochastic

namespace LinearStochastic
namespace AdjointCoefficients

/-- Literal real matrix input convention of the manuscript. -/
def fromMatrices {n r m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    AdjointCoefficients (𝕜 := ℝ) (E := Fin n → ℝ) (U := Fin r → ℝ) (ι := Fin m) where
  A := A.transpose.toLin'
  B := B.transpose.toLin'
  C := fun i => (C i).transpose.toLin'
  D := fun i => (D i).transpose.toLin'

/-- Paper `lem:flag` for its real matrix coefficients and its literal step n. -/
theorem matrix_flag_lemma {n r m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin m → Matrix (Fin n) (Fin r) ℝ) :
    let s := fromMatrices A B C D
    Antitone s.flag ∧ (∀ l, s.flag (n + l) = s.flag n) ∧
      s.HasInvariantSelectors (s.flag n) ∧
      (∀ V, s.HasInvariantSelectors V → V ≤ s.flag n) := by
  simpa using (fromMatrices A B C D).flag_lemma

/-- A sanity specialization: zero coefficients leave every subspace fixed. -/
theorem zero_obstruction {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (V : Submodule ℝ E) :
    (AdjointCoefficients.mk (0 : E →ₗ[ℝ] E) (0 : E →ₗ[ℝ] E)
      (fun _ : ι => 0) (fun _ : ι => 0)).obstruction V = V := by
  apply le_antisymm
  · exact obstruction_le _ V
  · intro v hv
    exact ⟨hv, fun _ => 0, by simp⟩

#print axioms matrix_flag_lemma
end AdjointCoefficients
end LinearStochastic
