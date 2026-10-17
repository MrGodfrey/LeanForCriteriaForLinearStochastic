module

public import Mathlib

@[expose] public section

/-!
Deterministic scalar estimates in the switching proof of
`thm:null-feedback`, equations `eq:aj` and `eq:switching-energy`.
The contraction and energy estimates below are explicit inputs. No SDE,
Itô estimate, feasible feedback, or terminal-state existence is assumed
to have been formalized by proving these scalar consequences.
-/

namespace LinearStochastic.Switching

open Filter Topology

theorem geometric_decay (b : ℕ → ℝ)
    (hstep : ∀ j, b (j + 1) ≤ (1 / 2 : ℝ) * b j) :
    ∀ j, b j ≤ (1 / 2 : ℝ) ^ j * b 0 := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    calc
      b (j + 1) ≤ (1 / 2 : ℝ) * b j := hstep j
      _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ j * b 0) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (1 / 2 : ℝ) ^ (j + 1) * b 0 := by ring

theorem quotient_decay (b : ℕ → ℝ) {rate : ℝ} (hrate : 0 < rate)
    (hstep : ∀ j, b (j + 1) ≤ (1 / 2 : ℝ) * b j) (j : ℕ) :
    b j / (4 ^ j * rate) ≤ (1 / 8 : ℝ) ^ j * (b 0 / rate) := by
  have hd : 0 < (4 : ℝ) ^ j * rate := mul_pos (by positivity) hrate
  calc
    b j / (4 ^ j * rate) ≤ ((1 / 2 : ℝ) ^ j * b 0) / (4 ^ j * rate) :=
      div_le_div_of_nonneg_right (geometric_decay b hstep j) hd.le
    _ = (1 / 8 : ℝ) ^ j * (b 0 / rate) := by
      rw [show (1 / 8 : ℝ) ^ j = (1 / 2 : ℝ) ^ j / 4 ^ j by
        rw [← div_pow]; congr 1; norm_num]
      ring

theorem energy_summable_and_bound (b e : ℕ → ℝ) (M rate : ℝ)
    (hrate : 0 < rate) (hb : ∀ j, 0 ≤ b j) (he : ∀ j, 0 ≤ e j)
    (hstep : ∀ j, b (j + 1) ≤ (1 / 2 : ℝ) * b j)
    (henergy : ∀ j, e j ≤ M ^ 2 * (b j / (4 ^ j * rate))) :
    Summable e ∧ (∑' j, e j) ≤ (8 / 7 : ℝ) * M ^ 2 * b 0 / rate := by
  let c := M ^ 2 * (b 0 / rate)
  have hc : 0 ≤ c := mul_nonneg (sq_nonneg M) (div_nonneg (hb 0) hrate.le)
  have hgeo : Summable (fun j : ℕ => c * (1 / 8 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
      (by norm_num : (1 / 8 : ℝ) < 1)).mul_left c
  have hbound : ∀ j, e j ≤ c * (1 / 8 : ℝ) ^ j := by
    intro j
    calc
      e j ≤ M ^ 2 * (b j / (4 ^ j * rate)) := henergy j
      _ ≤ M ^ 2 * ((1 / 8 : ℝ) ^ j * (b 0 / rate)) :=
        mul_le_mul_of_nonneg_left (quotient_decay b hrate hstep j) (sq_nonneg M)
      _ = c * (1 / 8 : ℝ) ^ j := by dsimp [c]; ring
  have hs : Summable e := Summable.of_nonneg_of_le he hbound hgeo
  refine ⟨hs, (hs.tsum_le_tsum hbound hgeo).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 8)
    (by norm_num : (1 / 8 : ℝ) < 1)]
  dsimp [c]
  ring

theorem state_sequence_tends_to_zero (a b : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j ≤ b j)
    (hstep : ∀ j, b (j + 1) ≤ (1 / 2 : ℝ) * b j) :
    Tendsto a atTop (𝓝 0) := by
  have hlim : Tendsto (fun j : ℕ => (1 / 2 : ℝ) ^ j * b 0) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const (b 0)
  exact squeeze_zero ha (fun j => (hab j).trans (geometric_decay b hstep j)) hlim

noncomputable def switchTime (T : ℝ) (j : ℕ) : ℝ := T * (1 - (1 / 2 : ℝ) ^ j)

theorem switchTime_zero (T : ℝ) : switchTime T 0 = 0 := by simp [switchTime]

theorem switchTime_length (T : ℝ) (j : ℕ) :
    switchTime T (j + 1) - switchTime T j = T * (1 / 2 : ℝ) ^ (j + 1) := by
  simp only [switchTime, pow_succ]
  ring

theorem switchTime_strictMono {T : ℝ} (hT : 0 < T) : StrictMono (switchTime T) := by
  apply strictMono_nat_of_lt_succ
  intro j
  have := mul_pos hT (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (j + 1))
  rw [← switchTime_length] at this
  linarith

theorem switchTime_tendsto (T : ℝ) : Tendsto (switchTime T) atTop (𝓝 T) := by
  change Tendsto (fun j : ℕ => T * (1 - (1 / 2 : ℝ) ^ j)) atTop (𝓝 T)
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  simpa [switchTime] using ((tendsto_const_nhds (x := (1 : ℝ))).sub h).const_mul T

/-- The exponential dominates the polynomial, uniformly for x ≥ 1. -/
theorem polynomial_exp_bound (p : ℕ) {L x : ℝ}
    (hL : 4 * (p : ℝ) ≤ L) (hx : 1 ≤ x) :
    x ^ (2 * p) * Real.exp (-L * x / 2) ≤ Real.exp (-L / 2) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog := Real.log_le_sub_one_of_pos hxpos
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (2 * p : ℝ) by positivity)
  have hexp : (2 * p : ℝ) * Real.log x + (-L * x / 2) ≤ -L / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) (sub_nonneg.mpr hx)]
  calc
    x ^ (2 * p) * Real.exp (-L * x / 2) =
        Real.exp ((2 * p : ℝ) * Real.log x + (-L * x / 2)) := by
      have hcast : (2 * p : ℝ) = ((2 * p : ℕ) : ℝ) := by norm_cast
      rw [Real.exp_add, hcast, Real.exp_nat_mul, Real.exp_log hxpos]
    _ ≤ Real.exp (-L / 2) := Real.exp_le_exp.mpr hexp

/-- There is a single L meeting all three scalar constraints in Step 1. -/
theorem exists_switching_constant (M : ℝ) (p : ℕ) :
    ∃ L : ℝ, 1 ≤ L ∧ 4 * (p : ℝ) ≤ L ∧
      4 ^ (2 * p) * M * L ^ p * Real.exp (-L / 2) ≤ (1 / 2 : ℝ) := by
  have ht : Tendsto (fun L : ℝ => 4 ^ (2 * p) * M *
      (L ^ p * Real.exp (-L / 2))) atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p : ℝ)
      (1 / 2 : ℝ) (by norm_num)
    simpa [Real.rpow_natCast, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      h.const_mul (4 ^ (2 * p) * M)
  have he : ∀ᶠ L : ℝ in atTop,
      4 ^ (2 * p) * M * (L ^ p * Real.exp (-L / 2)) < 1 / 2 :=
    ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  obtain ⟨L, h₁, h₂, h₃⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and
      ((eventually_ge_atTop (4 * (p : ℝ))).and he)).exists
  exact ⟨L, h₁, h₂, by nlinarith [h₃]⟩

/-- Passage from the state recurrence to the rescaled recurrence (eq:aj). -/
theorem rescaled_contraction (a rate len : ℕ → ℝ) (M : ℝ) (p : ℕ)
    (ha : ∀ j, 0 ≤ a j) (hrate : ∀ j, 0 ≤ rate j)
    (hratio : ∀ j, rate (j + 1) = 4 * rate j)
    (hstate : ∀ j, a (j + 1) ≤ M * rate j ^ p * Real.exp (-rate j * len j) * a j)
    (hfactor : ∀ j, 4 ^ (2 * p) * M * rate j ^ p *
      Real.exp (-rate j * len j) ≤ (1 / 2 : ℝ)) :
    ∀ j, rate (j + 1) ^ (2 * p) * a (j + 1) ≤
      (1 / 2 : ℝ) * (rate j ^ (2 * p) * a j) := by
  intro j
  calc
    rate (j + 1) ^ (2 * p) * a (j + 1) ≤
        rate (j + 1) ^ (2 * p) *
          (M * rate j ^ p * Real.exp (-rate j * len j) * a j) :=
      mul_le_mul_of_nonneg_left (hstate j) (pow_nonneg (hrate _) _)
    _ = (4 ^ (2 * p) * M * rate j ^ p * Real.exp (-rate j * len j)) *
        (rate j ^ (2 * p) * a j) := by rw [hratio, mul_pow]; ring
    _ ≤ (1 / 2 : ℝ) * (rate j ^ (2 * p) * a j) :=
      mul_le_mul_of_nonneg_right (hfactor j) (mul_nonneg (pow_nonneg (hrate _) _) (ha _))

/-- A continuous extension, if constructed in the state theory, has zero terminal energy. -/
theorem terminal_value_zero_of_continuous (f : ℝ → ℝ) (T : ℝ)
    (hcontinuous : ContinuousAt f T)
    (hzero : Tendsto (fun j : ℕ => f (switchTime T j)) atTop (𝓝 0)) :
    f T = 0 := by
  exact tendsto_nhds_unique (hcontinuous.tendsto.comp (switchTime_tendsto T)) hzero

end LinearStochastic.Switching
