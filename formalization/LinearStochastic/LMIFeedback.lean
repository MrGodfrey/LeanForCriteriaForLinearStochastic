module

public import LinearStochastic.LMICoefficients

@[expose] public section

noncomputable section
namespace LinearStochastic.LMIFeedback
open scoped BigOperators
open ConeBlocks LMICoefficients
variable {E U ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [Fintype ι] [DecidableEq ι]

theorem positive_injective (P : E →ₗ[ℝ] E)
    (hP : PositiveCone.UniformPositive P.toContinuousLinearMap) : Function.Injective P := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro x hx
  change x = 0
  by_contra hn
  have hp := PositiveCone.uniformPositive_strict _ hP x hn
  have hz : P x = 0 := hx
  change 0 < inner ℝ (P x) x at hp
  simp [hz] at hp

/-- The actual inverse, obtained from proved injectivity in finite dimension. -/
def inverse (P : E →ₗ[ℝ] E) (hP : PositiveCone.UniformPositive P.toContinuousLinearMap) :
    E →ₗ[ℝ] E := (LinearEquiv.ofInjectiveEndo P (positive_injective P hP)).symm.toLinearMap

@[simp] theorem apply_inverse (P : E →ₗ[ℝ] E)
    (hP : PositiveCone.UniformPositive P.toContinuousLinearMap) (x : E) :
    P (inverse P hP x) = x :=
  (LinearEquiv.ofInjectiveEndo P (positive_injective P hP)).apply_symm_apply x

@[simp] theorem inverse_apply (P : E →ₗ[ℝ] E)
    (hP : PositiveCone.UniformPositive P.toContinuousLinearMap) (x : E) :
    inverse P hP (P x) = x :=
  (LinearEquiv.ofInjectiveEndo P (positive_injective P hP)).symm_apply_apply x

theorem inverse_symmetric (P : E →ₗ[ℝ] E) (hs : P.IsSymmetric)
    (hP : PositiveCone.UniformPositive P.toContinuousLinearMap) :
    (inverse P hP).IsSymmetric := by
  intro x y
  have h := hs (inverse P hP x) (inverse P hP y)
  simpa using h.symm

theorem inverse_strict (P : E →ₗ[ℝ] E)
    (hP : PositiveCone.UniformPositive P.toContinuousLinearMap) (x : E) (hx : x ≠ 0) :
    0 < inner ℝ (inverse P hP x) x := by
  have hn : inverse P hP x ≠ 0 := by
    intro hz
    have hh := apply_inverse P hP x
    simp only [hz, map_zero] at hh
    exact hx hh.symm
  have hp := PositiveCone.uniformPositive_strict _ hP (inverse P hP x) hn
  change 0 < inner ℝ (P (inverse P hP x)) (inverse P hP x) at hp
  rw [apply_inverse, real_inner_comm] at hp
  exact hp

theorem liftBlock_inner (i j : ι) (T : E →ₗ[ℝ] E) (z : BlockSpace E ι) :
    inner ℝ (liftBlock i j T z) z = inner ℝ (T (project j z)) (project i z) := by
  change inner ℝ (inject i (T (project j z))) z = _
  rw [← LinearMap.adjoint_inner_right, inject_adjoint]

/-- The actual block LMI quadratic form, before choosing any test vector. -/
theorem lmi_quadratic
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U)
    (z : BlockSpace E (Option ι)) :
    inner ℝ (lmi A B C D ρ P K z) z =
      inner ℝ ((A.comp P + P.comp A.adjoint + B.comp K + K.adjoint.comp B.adjoint + ρ • P)
        (project none z)) (project none z) +
      ∑ i, (2 * inner ℝ (((C i).comp P + (D i).comp K) (project none z))
        (project (some i) z) - inner ℝ (P (project (some i) z)) (project (some i) z)) := by
  simp only [lmi, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.sub_apply,
    inner_add_left, sum_inner, inner_sub_left, liftBlock_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [LinearMap.adjoint_inner_left, LinearMap.add_apply, inner_add_right, real_inner_comm]
  ring

theorem head_quadratic (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (ρ : ℝ) (P : E →ₗ[ℝ] E) (hP : P.IsSymmetric) (K : E →ₗ[ℝ] U) (y : E) :
    inner ℝ ((A.comp P + P.comp A.adjoint + B.comp K + K.adjoint.comp B.adjoint + ρ • P) y) y =
      2 * inner ℝ (A (P y) + B (K y)) y + ρ * inner ℝ (P y) y := by
  have hp : inner ℝ (P (A.adjoint y)) y = inner ℝ (A (P y)) y := by
    rw [hP, LinearMap.adjoint_inner_left, real_inner_comm]
  have hk : inner ℝ (K.adjoint (B.adjoint y)) y = inner ℝ (B (K y)) y := by
    rw [LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left, real_inner_comm]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    inner_add_left, inner_smul_left, hp, hk, conj_trivial]
  ring

/-- A genuine vector in the state/noise Hilbert direct sum. -/
def testVector (x : E) (y : ι → E) : BlockSpace E (Option ι) :=
  WithLp.toLp 2 (fun i => match i with | none => x | some j => y j)

@[simp] theorem project_test_none (x : E) (y : ι → E) :
    project none (testVector x y) = x := rfl

@[simp] theorem project_test_some (x : E) (y : ι → E) (i : ι) :
    project (some i) (testVector x y) = y i := rfl

/-- The Schur test is evaluated exactly, with the genuine inverse of P. -/
theorem feedback_test_quadratic
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (hs : P.IsSymmetric)
    (hP : PositiveCone.UniformPositive P.toContinuousLinearMap) (K : E →ₗ[ℝ] U) (x : E) :
    let H := inverse P hP
    let N := fun i => C i x + D i (K (H x))
    let z := testVector (H x) (fun i => H (N i))
    inner ℝ (lmi A B C D ρ P K z) z =
      2 * inner ℝ (A x + B (K (H x))) (H x) + ρ * inner ℝ x (H x) +
      ∑ i, inner ℝ (N i) (H (N i)) := by
  dsimp only
  rw [lmi_quadratic, head_quadratic A B ρ P hs K]
  simp only [project_test_none, project_test_some, apply_inverse,
    LinearMap.add_apply, LinearMap.comp_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The LMI produces the actual closed-loop Lyapunov inequality for the
feedback K P⁻¹. This is a deterministic quadratic statement, not an assumed
stochastic decay estimate. -/
theorem closed_loop_lyapunov
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (hs : P.IsSymmetric)
    (hP : PositiveCone.UniformPositive P.toContinuousLinearMap) (K : E →ₗ[ℝ] U)
    (hneg : PositiveCone.UniformPositive (-(lmi A B C D ρ P K).toContinuousLinearMap))
    (x : E) (hx : x ≠ 0) :
    let H := inverse P hP
    let N := fun i => C i x + D i (K (H x))
    2 * inner ℝ (A x + B (K (H x))) (H x) + ρ * inner ℝ x (H x) +
      ∑ i, inner ℝ (N i) (H (N i)) < 0 := by
  let H := inverse P hP
  let N := fun i => C i x + D i (K (H x))
  let z := testVector (H x) (fun i => H (N i))
  have hz : z ≠ 0 := by
    intro hh
    have hh' := congrArg (project (E := E) none) hh
    change H x = 0 at hh'
    have h := apply_inverse P hP x
    change P (H x) = x at h
    rw [hh', map_zero] at h
    exact hx h.symm
  have h := PositiveCone.uniformPositive_strict _ hneg z hz
  change 0 < inner ℝ (-(lmi A B C D ρ P K z)) z at h
  rw [inner_neg_left] at h
  have hq := feedback_test_quadratic A B C D ρ P hs hP K x
  change inner ℝ (lmi A B C D ρ P K z) z = _ at hq
  rw [hq] at h
  exact neg_pos.mp h

/-- The inverse is uniformly positive; the bound is derived without a spectral theorem. -/
theorem inverse_uniformPositive (P : E →ₗ[ℝ] E)
    (hP : PositiveCone.UniformPositive P.toContinuousLinearMap) :
    PositiveCone.UniformPositive (inverse P hP).toContinuousLinearMap := by
  have hhP := hP
  obtain ⟨ε, hε, hb⟩ := hhP
  let c := 1 + ‖P.toContinuousLinearMap‖
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨ε / c^2, div_pos hε (sq_pos_of_pos hc), ?_⟩
  intro x
  have hn : ‖x‖ ≤ c * ‖inverse P hP x‖ := by
    calc
      ‖x‖ = ‖P (inverse P hP x)‖ := congrArg norm (apply_inverse P hP x).symm
      _ ≤ ‖P.toContinuousLinearMap‖ * ‖inverse P hP x‖ :=
        P.toContinuousLinearMap.le_opNorm _
      _ ≤ c * ‖inverse P hP x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        dsimp [c]
        linarith
  have hn2 := pow_le_pow_left₀ (norm_nonneg x) hn 2
  rw [mul_pow] at hn2
  have hh := hb (inverse P hP x)
  change ε * ‖inverse P hP x‖ ^ 2 ≤ inner ℝ (P (inverse P hP x)) (inverse P hP x) at hh
  rw [apply_inverse, real_inner_comm] at hh
  change ε / c^2 * ‖x‖^2 ≤ inner ℝ (inverse P hP x) x
  calc
    _ ≤ (ε / c^2) * (c^2 * ‖inverse P hP x‖^2) :=
      mul_le_mul_of_nonneg_left hn2 (div_nonneg hε.le (sq_nonneg c))
    _ = ε * ‖inverse P hP x‖^2 := by field_simp
    _ ≤ _ := hh

/-- Arbitrary-rate feedback and its genuine positive Lyapunov operator follow
from the original obstruction flag, with no stochastic or LQ premise. -/
theorem arbitrary_rate_feedback [Nonempty ι]
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E)
    (hflag : (InputStructure.fromForward A B C D).flag (Module.finrank ℝ E) = ⊥)
    (ρ : ℝ) :
    ∃ (H : E →ₗ[ℝ] E) (G : E →ₗ[ℝ] U), H.IsSymmetric ∧
      PositiveCone.UniformPositive H.toContinuousLinearMap ∧
      ∀ x, x ≠ 0 →
        2 * inner ℝ ((A + B.comp G) x) (H x) + ρ * inner ℝ x (H x) +
        ∑ i, inner ℝ ((C i + (D i).comp G) x) (H ((C i + (D i).comp G) x)) < 0 := by
  obtain ⟨P, K, hs, hneg⟩ := arbitrary_rate_feasible A B C D hflag ρ
  have hP := positive_lyapunov_of_negative_lmi A B C D ρ P K hneg
  refine ⟨inverse P hP, K.comp (inverse P hP), inverse_symmetric P hs hP,
    inverse_uniformPositive P hP, ?_⟩
  intro x hx
  exact closed_loop_lyapunov A B C D ρ P hs hP K hneg x hx

#print axioms arbitrary_rate_feedback
#print axioms inverse_uniformPositive
#print axioms closed_loop_lyapunov
end LinearStochastic.LMIFeedback




