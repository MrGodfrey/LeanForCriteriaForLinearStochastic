import LinearStochastic.AlgebraFlag

/-!
# Finite products and the smallest common invariant subspace

This is the algebraic finite-word argument in `prop:exact-rank`. It does not
assume stochastic controllability or the reduction from surjective diffusion.
-/
noncomputable section
namespace LinearStochastic
namespace Words
open Module

variable {𝕜 E ι : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable (M : ι → E →ₗ[𝕜] E)

/-- Add the images under every generator. -/
def step (W : Submodule 𝕜 E) : Submodule 𝕜 E := W ⊔ ⨆ i, W.map (M i)

/-- Common invariance under exactly the supplied coefficient maps. -/
def Invariant (W : Submodule 𝕜 E) : Prop := ∀ i, W.map (M i) ≤ W

theorem le_step (W : Submodule 𝕜 E) : W ≤ step M W := le_sup_left

theorem step_mono : Monotone (step M) := by
  intro V W h
  exact sup_le_sup h (iSup_mono fun i => Submodule.map_mono h)

theorem step_eq_iff_invariant (W : Submodule 𝕜 E) : step M W = W ↔ Invariant M W := by
  simp only [step, sup_eq_left, iSup_le_iff, Invariant]

/-- S₀ = H, Sₖ₊₁ = Sₖ + Σ MᵢSₖ, without a built-in stopping rule. -/
def reach (H : Submodule 𝕜 E) (k : ℕ) : Submodule 𝕜 E := Nat.rec H (fun _ V => step M V) k

@[simp] theorem reach_zero (H : Submodule 𝕜 E) : reach M H 0 = H := rfl
@[simp] theorem reach_succ (H : Submodule 𝕜 E) (k : ℕ) :
    reach M H (k + 1) = step M (reach M H k) := rfl

theorem reach_step_le (H : Submodule 𝕜 E) (k : ℕ) : reach M H k ≤ reach M H (k + 1) :=
  le_step M _

theorem reach_mono (H : Submodule 𝕜 E) : Monotone (reach M H) :=
  monotone_nat_of_le_succ (reach_step_le M H)

theorem seed_le_reach (H : Submodule 𝕜 E) (k : ℕ) : H ≤ reach M H k :=
  reach_mono M H (Nat.zero_le k)

theorem stationary_of_step_eq {H : Submodule 𝕜 E} {k : ℕ}
    (h : reach M H (k + 1) = reach M H k) (l : ℕ) : reach M H (k + l) = reach M H k := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [show k + (l + 1) = (k + l) + 1 by omega, reach_succ, ih, ← reach_succ, h]

@[simp] theorem reach_bot (k : ℕ) : reach M (⊥ : Submodule 𝕜 E) k = ⊥ := by
  induction k with
  | zero => rfl
  | succ k ih => simp [reach_succ, ih, step]

theorem reach_le_invariant {H U : Submodule 𝕜 E} (hH : H ≤ U) (hU : Invariant M U) (k : ℕ) :
    reach M H k ≤ U := by
  induction k with
  | zero => exact hH
  | succ k ih =>
    change reach M H k ⊔ ⨆ i, (reach M H k).map (M i) ≤ U
    exact sup_le ih (iSup_le fun i => (Submodule.map_mono ih).trans (hU i))

/-- Products in their actual left-to-right order; the empty word is the identity. -/
def wordMap : List ι → E →ₗ[𝕜] E
  | [] => LinearMap.id
  | i :: w => (M i).comp (wordMap w)

@[simp] theorem wordMap_nil : wordMap M [] = LinearMap.id := rfl
@[simp] theorem wordMap_cons (i : ι) (w : List ι) : wordMap M (i :: w) = (M i).comp (wordMap M w) := rfl

/-- Span of images of the seed under all words of length at most k. -/
def wordSpan (H : Submodule 𝕜 E) (k : ℕ) : Submodule 𝕜 E :=
  ⨆ w : List ι, ⨆ (_ : w.length ≤ k), H.map (wordMap M w)

theorem wordSpan_mono (H : Submodule 𝕜 E) : Monotone (wordSpan M H) := by
  intro k l h
  refine iSup_le fun w => iSup_le fun hw => ?_
  exact le_iSup_of_le w (le_iSup_of_le (hw.trans h) le_rfl)

theorem seed_le_wordSpan (H : Submodule 𝕜 E) (k : ℕ) : H ≤ wordSpan M H k := by
  have h : H.map (wordMap M []) ≤ wordSpan M H k :=
    le_iSup_of_le [] (le_iSup_of_le (by simp : [].length ≤ k) le_rfl)
  simpa using h

@[simp] theorem wordSpan_zero (H : Submodule 𝕜 E) : wordSpan M H 0 = H := by
  apply le_antisymm
  · refine iSup_le fun w => iSup_le fun hw => ?_
    have hw0 : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    simp [hw0]
  · exact seed_le_wordSpan M H 0

theorem wordSpan_succ (H : Submodule 𝕜 E) (k : ℕ) :
    wordSpan M H (k + 1) = step M (wordSpan M H k) := by
  apply le_antisymm
  · refine iSup_le fun w => iSup_le fun hw => ?_
    cases w with
    | nil => simpa using (seed_le_wordSpan M H k).trans (le_step M _)
    | cons i w =>
      have hw' : w.length ≤ k := by simpa using hw
      have hwi : H.map (wordMap M w) ≤ wordSpan M H k :=
        le_iSup_of_le w (le_iSup_of_le hw' le_rfl)
      rw [wordMap_cons, Submodule.map_comp]
      exact (Submodule.map_mono hwi).trans ((le_iSup (fun j => (wordSpan M H k).map (M j)) i).trans le_sup_right)
  · apply sup_le
    · exact wordSpan_mono M H (Nat.le_succ k)
    · refine iSup_le fun i => ?_
      rw [wordSpan, Submodule.map_iSup]
      refine iSup_le fun w => ?_
      rw [Submodule.map_iSup]
      refine iSup_le fun hw => ?_
      rw [← Submodule.map_comp, ← wordMap_cons]
      exact le_iSup_of_le (i :: w) (le_iSup_of_le (by simpa using Nat.succ_le_succ hw) le_rfl)

/-- The recursive spaces consist exactly of words of bounded length. -/
theorem reach_eq_wordSpan (H : Submodule 𝕜 E) (k : ℕ) : reach M H k = wordSpan M H k := by
  induction k with
  | zero => simp
  | succ k ih => rw [reach_succ, wordSpan_succ, ih]

/-- Images of the seed under words of exactly k factors. -/
def layer (H : Submodule 𝕜 E) (k : ℕ) : Submodule 𝕜 E :=
  Nat.rec H (fun _ V => ⨆ i, V.map (M i)) k

@[simp] theorem layer_zero (H : Submodule 𝕜 E) : layer M H 0 = H := rfl
@[simp] theorem layer_succ (H : Submodule 𝕜 E) (k : ℕ) :
    layer M H (k + 1) = ⨆ i, (layer M H k).map (M i) := rfl

/-- The cumulative union of the exact-length layers. -/
def cumulative (H : Submodule 𝕜 E) (k : ℕ) : Submodule 𝕜 E :=
  Nat.rec H (fun k V => V ⊔ layer M H (k + 1)) k

@[simp] theorem cumulative_zero (H : Submodule 𝕜 E) : cumulative M H 0 = H := rfl
@[simp] theorem cumulative_succ (H : Submodule 𝕜 E) (k : ℕ) :
    cumulative M H (k + 1) = cumulative M H k ⊔ layer M H (k + 1) := rfl

theorem step_sup (V W : Submodule 𝕜 E) : step M (V ⊔ W) = step M V ⊔ step M W := by
  simp only [step, Submodule.map_sup, iSup_sup_eq]
  ac_rfl

theorem step_cumulative (H : Submodule 𝕜 E) (k : ℕ) :
    step M (cumulative M H k) = cumulative M H (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [cumulative_succ, step_sup, ih, cumulative_succ, step, ← layer_succ]
    simp only [cumulative_succ, sup_assoc, sup_left_idem]

theorem cumulative_eq_reach (H : Submodule 𝕜 E) (k : ℕ) :
    cumulative M H k = reach M H k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← step_cumulative, reach_succ, ih]

variable [FiniteDimensional 𝕜 E]

/-- The n−1 bound, including the zero-seed and zero-dimensional cases. -/
theorem stable_at_finrank_sub_one (H : Submodule 𝕜 E) :
    reach M H (finrank 𝕜 E - 1 + 1) = reach M H (finrank 𝕜 E - 1) := by
  by_cases hH : H = ⊥
  · simp [hH, step]
  by_contra hn
  have hd : 0 < finrank 𝕜 H := Nat.pos_of_ne_zero (fun h => hH (Submodule.finrank_eq_zero.mp h))
  have hdn := H.finrank_le
  have strict (k : ℕ) (hk : k ≤ finrank 𝕜 E - 1) : reach M H k < reach M H (k + 1) := by
    refine lt_of_le_of_ne (reach_step_le M H k) ?_
    intro heq
    have h1 := stationary_of_step_eq M heq.symm (finrank 𝕜 E - 1 - k)
    have h2 := stationary_of_step_eq M heq.symm (finrank 𝕜 E - 1 + 1 - k)
    have hk1 : k + (finrank 𝕜 E - 1 - k) = finrank 𝕜 E - 1 := by omega
    have hk2 : k + (finrank 𝕜 E - 1 + 1 - k) = finrank 𝕜 E - 1 + 1 := by omega
    rw [hk1] at h1
    rw [hk2] at h2
    exact hn (h2.trans h1.symm)
  have bound : ∀ k, k ≤ finrank 𝕜 E - 1 + 1 → finrank 𝕜 H + k ≤ finrank 𝕜 (reach M H k) := by
    intro k
    induction k with
    | zero => intro _; change finrank 𝕜 H + 0 ≤ finrank 𝕜 H; omega
    | succ k ih =>
      intro hk
      have hi := ih (by omega)
      have hs := Submodule.finrank_lt_finrank_of_lt (strict k (by omega))
      omega
  have hb := bound (finrank 𝕜 E - 1 + 1) le_rfl
  have hu := (reach M H (finrank 𝕜 E - 1 + 1)).finrank_le
  omega

/-- The entire common invariant envelope is generated by words of length ≤ n−1. -/
theorem finite_word_envelope (H : Submodule 𝕜 E) :
    Invariant M (wordSpan M H (finrank 𝕜 E - 1)) ∧
    H ≤ wordSpan M H (finrank 𝕜 E - 1) ∧
    (∀ U, H ≤ U → Invariant M U → wordSpan M H (finrank 𝕜 E - 1) ≤ U) := by
  rw [← reach_eq_wordSpan]
  refine ⟨(step_eq_iff_invariant M _).mp (stable_at_finrank_sub_one M H), seed_le_reach M H _, ?_⟩
  intro U hH hU
  exact reach_le_invariant M hH hU _

#print axioms finite_word_envelope
end Words
end LinearStochastic

namespace LinearStochastic.Words
open Module
open scoped InnerProductSpace

variable {E F ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Taking the orthogonal complement exchanges invariance with adjoint invariance. -/
theorem orthogonal_invariant (M : ι → E →ₗ[ℝ] E) {V : Submodule ℝ E}
    (h : Invariant M V) : Invariant (fun i => (M i).adjoint) Vᗮ := by
  intro i z hz
  obtain ⟨v, hv, rfl⟩ := hz
  rw [Submodule.mem_orthogonal]
  intro x hx
  rw [LinearMap.adjoint_inner_right]
  exact (V.mem_orthogonal v).mp hv (M i x) (h i ⟨x, hx, rfl⟩)

/-- The orthogonal complement of the word envelope is precisely the greatest
adjoint-invariant subspace annihilating the seed. -/
theorem orthogonal_wordSpan_greatest (M : ι → E →ₗ[ℝ] E) (H : Submodule ℝ E) :
    let Z := (wordSpan M H (finrank ℝ E - 1))ᗮ
    Invariant (fun i => (M i).adjoint) Z ∧ Z ≤ Hᗮ ∧
      (∀ V, Invariant (fun i => (M i).adjoint) V → V ≤ Hᗮ → V ≤ Z) := by
  obtain ⟨hI, hH, hmin⟩ := finite_word_envelope M H
  refine ⟨orthogonal_invariant M hI, Submodule.orthogonal_le hH, ?_⟩
  intro V hV hVH
  have hi : Invariant M Vᗮ := by
    simpa only [LinearMap.adjoint_adjoint] using
      orthogonal_invariant (fun i => (M i).adjoint) hV
  have hh : H ≤ Vᗮ := by
    simpa only [Submodule.orthogonal_orthogonal] using Submodule.orthogonal_le hVH
  have hm := Submodule.orthogonal_le (hmin Vᗮ hh hi)
  simpa only [Submodule.orthogonal_orthogonal] using hm

/-- The same maximality statement with the seed written as an actual input map H:
its annihilator is ker H†, exactly the manuscript's kernel condition. -/
theorem orthogonal_wordRange_greatest (M : ι → E →ₗ[ℝ] E) (H : F →ₗ[ℝ] E) :
    let Z := (wordSpan M H.range (finrank ℝ E - 1))ᗮ
    Invariant (fun i => (M i).adjoint) Z ∧ Z ≤ H.adjoint.ker ∧
      (∀ V, Invariant (fun i => (M i).adjoint) V → V ≤ H.adjoint.ker → V ≤ Z) := by
  simpa only [H.orthogonal_range] using orthogonal_wordSpan_greatest M H.range

#print axioms orthogonal_wordRange_greatest
end LinearStochastic.Words
