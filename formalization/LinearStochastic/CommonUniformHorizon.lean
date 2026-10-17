module

public import LinearStochastic.CommonPicardHorizon

@[expose] public section

/-! Filtration-independent short-time bounds and a genuine finite equal mesh
for every finite horizon. -/
set_option autoImplicit false
noncomputable section
namespace LinearStochastic.CommonUniformHorizon
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
open CommonPicardHorizon
variable {κ ι : Type*} [Fintype κ] [Fintype ι]

def bound (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) : ℝ :=
  (T:ℝ)*matrixSize A + Real.sqrt (T:ℝ)*∑ i, matrixSize (C i)

theorem bound_mono (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) :
    Monotone (fun T ↦ bound T A C) := by
  intro s t h
  exact add_le_add (mul_le_mul_of_nonneg_right (show (s:ℝ) ≤ t from h) (matrixSize_nonneg A))
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt h) (Finset.sum_nonneg fun i _ ↦ matrixSize_nonneg (C i)))

/-- The positive contraction bound is uniform over all restarted filtrations
and probability spaces because it uses only the literal matrix entries. -/
theorem exists_positive_bound (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) :
    ∃ δ : ℝ≥0, 0 < δ ∧ bound δ A C < 1 := by
  let a := matrixSize A
  let c := ∑ i, matrixSize (C i)
  have ha : 0 ≤ a := matrixSize_nonneg A
  have hc : 0 ≤ c := Finset.sum_nonneg fun i _ ↦ matrixSize_nonneg (C i)
  let h : ℝ := 1 / (4 * (a+c+1))
  have hpos : 0 < h := by dsimp [h]; positivity
  have hle : h ≤ 1 := by
    dsimp [h]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hmul : h * (a+c+1) = 1/4 := by dsimp [h]; field_simp
  let δ : ℝ≥0 := ⟨h^2,sq_nonneg h⟩
  refine ⟨δ, by change 0 < h^2; positivity, ?_⟩
  have hroot : Real.sqrt (δ:ℝ) = h := Real.sqrt_sq hpos.le
  have hδ : (δ:ℝ) ≤ h := by change h^2 ≤ h; nlinarith
  change (δ:ℝ)*a+Real.sqrt (δ:ℝ)*c < 1
  rw [hroot]
  nlinarith [mul_le_mul_of_nonneg_right hδ ha]

/-- Every finite horizon admits an actual finite equal mesh satisfying the
same strict bound. The number of intervals is positive even when T=0. -/
theorem exists_mesh (T : ℝ≥0) (A : Matrix κ κ ℝ) (C : ι → Matrix κ κ ℝ) :
    ∃ N : ℕ, 0 < N ∧ bound (T / (N:ℝ≥0)) A C < 1 := by
  obtain ⟨δ,hδ,hb⟩ := exists_positive_bound A C
  obtain ⟨n,hn⟩ := exists_nat_gt ((T:ℝ)/(δ:ℝ))
  refine ⟨n+1,Nat.succ_pos n,?_⟩
  have hd : 0 < (δ:ℝ) := hδ
  have hN : (0:ℝ) < n+1 := by positivity
  have hT : (T:ℝ) < (n:ℝ)*δ := (div_lt_iff₀ hd).mp hn
  have hm : T / ((n+1:ℕ):ℝ≥0) ≤ δ := by
    apply (div_le_iff₀ (by positivity)).mpr
    exact_mod_cast (show (T:ℝ) ≤ (δ:ℝ)*((n:ℝ)+1) by nlinarith)
  exact (bound_mono A C hm).trans_lt hb
end LinearStochastic.CommonUniformHorizon
