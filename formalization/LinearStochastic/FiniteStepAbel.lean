/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho

The finite-grid Abel argument is adapted from MathFin WienerExponentialTotality
and separated as a purely algebraic vector-valued time-grid statement.
-/
import MathFin.Foundations.WienerExponentialTotality

noncomputable section
namespace LinearStochastic.FiniteStepAbel
open scoped NNReal BigOperators

/-- Every finite vector coordinate linear form at times in `[0,T]` is a
vector step-increment linear form, on a common monotone grid starting at zero.
This is pure finite summation, independent of probability and representation. -/
theorem exists_step_sum {ι J : Type*} [Fintype ι] [Fintype J]
    (T : ℝ≥0) (t : J → ℝ≥0) (htT : ∀ j, t j ≤ T) (lam : ι → J → ℝ) :
    ∃ (s : ℕ → ℝ≥0) (N : ℕ) (c : ℕ → ι → ℝ),
      Monotone s ∧ s 0 = 0 ∧ s N = T ∧
      ∀ (X : ι → ℝ≥0 → ℝ), (∀ i, X i 0 = 0) →
        (∑ k ∈ Finset.range N, ∑ i, c k i * (X i (s (k+1)) - X i (s k))) =
          ∑ i, ∑ j, lam i j * X i (t j) := by
  classical
  set S : Finset ℝ≥0 := insert 0 (insert T (Finset.image t Finset.univ))
  have h0S : (0 : ℝ≥0) ∈ S := Finset.mem_insert_self _ _
  have hTS : T ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have htS (j : J) : t j ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem t (Finset.mem_univ j)))
  have hSle (q : ℝ≥0) (hq : q ∈ S) : q ≤ T := by
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact zero_le
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact le_rfl
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
    exact htT j
  have hcard : 0 < S.card := Finset.card_pos.mpr ⟨0,h0S⟩
  set m : ℕ := S.card with hm
  set N : ℕ := m-1 with hN
  set e : Fin m ↪o ℝ≥0 := S.orderEmbOfFin rfl with he
  have hlt (k : ℕ) : min k N < m := by omega
  set s : ℕ → ℝ≥0 := fun k => e ⟨min k N,hlt k⟩ with hsdef
  have hsval (k : ℕ) (hk : k ≤ N) : s k = e ⟨k,by omega⟩ := by
    simp only [hsdef]
    exact congrArg e (Fin.val_injective (min_eq_left hk))
  have hsmono : Monotone s := fun a b hab => e.monotone (by simp only [Fin.mk_le_mk]; omega)
  have hs0 : s 0 = 0 := by
    have h1 : s 0 = S.min' ⟨0,h0S⟩ := by
      rw [hsval 0 (Nat.zero_le _)]
      exact Finset.orderEmbOfFin_zero (s := S) rfl hcard
    rw [h1]
    exact le_antisymm (Finset.min'_le S 0 h0S) zero_le
  have hsN : s N = T := by
    have h1 : s N = S.max' ⟨0,h0S⟩ := by
      rw [hsval N le_rfl]
      exact Finset.orderEmbOfFin_last (s := S) rfl hcard
    rw [h1]
    exact le_antisymm (Finset.max'_le S _ _ hSle) (Finset.le_max' S T hTS)
  let c : ℕ → ι → ℝ := fun k i => ∑ j, if s k < t j then lam i j else 0
  refine ⟨s,N,c,hsmono,hs0,hsN,?_⟩
  intro X hX0
  have hcell (i : ι) (j : J) :
      (∑ k ∈ Finset.range N, (if s k < t j then lam i j else 0) *
        (X i (s (k+1)) - X i (s k))) = lam i j * (X i (t j) - X i (s 0)) := by
    obtain ⟨q,hq⟩ : ∃ q : Fin m, e q = t j := by
      show t j ∈ Set.range e
      rw [he,Finset.range_orderEmbOfFin S rfl]
      exact htS j
    have hqlt := q.isLt
    have hqN : (q : ℕ) ≤ N := by omega
    have hsq : s (q : ℕ) = t j := by rw [hsval (q : ℕ) hqN,←hq]
    have hfilter : {k ∈ Finset.range N | s k < t j} = Finset.range (q : ℕ) := by
      ext k
      simp only [Finset.mem_filter,Finset.mem_range]
      constructor
      · rintro ⟨hk,hklt⟩
        rw [hsval k (by omega),←hq] at hklt
        exact Fin.lt_def.mp (e.lt_iff_lt.mp hklt)
      · intro hk
        refine ⟨by omega,?_⟩
        rw [hsval k (by omega),←hq]
        exact e.lt_iff_lt.mpr (Fin.lt_def.mpr hk)
    calc
      _ = ∑ k ∈ Finset.range N, if s k < t j then
          lam i j * (X i (s (k+1)) - X i (s k)) else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : s k < t j <;> simp [hk]
      _ = ∑ k ∈ {k ∈ Finset.range N | s k < t j},
          lam i j * (X i (s (k+1)) - X i (s k)) := (Finset.sum_filter _ _).symm
      _ = ∑ k ∈ Finset.range (q : ℕ), lam i j * (X i (s (k+1)) - X i (s k)) := by rw [hfilter]
      _ = lam i j * ∑ k ∈ Finset.range (q : ℕ), (X i (s (k+1)) - X i (s k)) := by rw [Finset.mul_sum]
      _ = lam i j * (X i (s (q : ℕ)) - X i (s 0)) := by
        rw [Finset.sum_range_sub (fun k => X i (s k))]
      _ = _ := by rw [hsq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∑ k ∈ Finset.range N, ∑ j, (if s k < t j then lam i j else 0) *
        (X i (s (k+1)) - X i (s k)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_mul _ _ _
    _ = ∑ j, ∑ k ∈ Finset.range N, (if s k < t j then lam i j else 0) *
        (X i (s (k+1)) - X i (s k)) := Finset.sum_comm
    _ = ∑ j, lam i j * (X i (t j) - X i (s 0)) := Finset.sum_congr rfl (fun j _ => hcell i j)
    _ = _ := by rw [hs0,hX0 i]; simp

end LinearStochastic.FiniteStepAbel
