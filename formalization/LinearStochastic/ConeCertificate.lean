module

public import LinearStochastic.AlgebraFlag

@[expose] public section

/-!
# Algebraic obstruction carried by a positive dual certificate

This proves the invariant-space step in the cone-separation alternative to
the stochastic LQ proof. A separating certificate is not postulated to exist:
its existence and block factorization are separate obligations. The theorem
below derives invariance from positivity and an explicit operator identity.
-/
noncomputable section
namespace LinearStochastic.ConeCertificate
open Module
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A positive operator has zero quadratic form only on its kernel. -/
theorem positive_quadratic_zero_iff (Q : E →ₗ[ℝ] E) (hQ : Q.IsPositive) (v : E) :
    inner ℝ (Q v) v = 0 ↔ Q v = 0 := by
  constructor
  · intro hv
    apply ext_inner_right ℝ
    intro y
    simp only [inner_zero_left]
    have hs : inner ℝ (Q y) v = inner ℝ (Q v) y := by
      rw [hQ.isSymmetric y v, real_inner_comm]
    have hquad : ∀ t : ℝ, 0 ≤ inner ℝ (Q y) y * (t * t) +
        (2 * inner ℝ (Q v) y) * t + 0 := by
      intro t
      have hp := hQ.inner_nonneg_left (v + t • y)
      simp only [map_add, map_smul, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, hv, hs] at hp
      nlinarith
    have hd := discrim_le_zero hquad
    simp only [discrim, mul_zero, sub_zero] at hd
    nlinarith [sq_nonneg (inner ℝ (Q v) y)]
  · intro hv
    simp [hv]

/-- Kernel invariance for the adjoint is equivalent to range invariance for
the map, with respect to a symmetric positive certificate. -/
theorem maps_range_of_adjoint_preserves_kernel (Q G : E →ₗ[ℝ] E)
    (hQ : Q.IsPositive) (hG : ∀ v, Q v = 0 → Q (G.adjoint v) = 0) :
    ∀ x ∈ Q.range, G x ∈ Q.range := by
  have hr : Q.range = Q.kerᗮ := by
    rw [LinearMap.orthogonal_ker, hQ.adjoint_eq]
  intro x hx
  rw [hr] at hx ⊢
  rw [Submodule.mem_orthogonal]
  intro v hv
  rw [← LinearMap.adjoint_inner_left]
  exact (Submodule.mem_orthogonal _ _).mp hx (G.adjoint v) (hG v hv)

variable {U ι : Type*} [AddCommGroup U] [Module ℝ U] [Fintype ι]

/-- The dual Lyapunov identity forces all selector maps, and the corrected
drift, to preserve `range Q`. It does not assume those invariances. -/
theorem dual_identity_invariant_selectors
    (s : AdjointCoefficients (𝕜 := ℝ) (E := E) (U := U) (ι := ι))
    (Q P : E →ₗ[ℝ] E) (Γ : ι → E →ₗ[ℝ] E) (ρ : ℝ)
    (hQ : Q.IsPositive) (hP : P.IsPositive)
    (hbalance :
      (s.A + ∑ i, (s.C i).comp (Γ i)).comp Q +
        Q.comp (s.A + ∑ i, (s.C i).comp (Γ i)).adjoint + ρ • Q =
          P + ∑ i, ((Γ i).comp Q).comp (Γ i).adjoint)
    (hinput : (s.B + ∑ i, (s.D i).comp (Γ i)).comp Q = 0) :
    s.HasInvariantSelectors Q.range := by
  let H := s.A + ∑ i, (s.C i).comp (Γ i)
  have hker (v : E) (hv : Q v = 0) :
      P v = 0 ∧ (∀ i, Q ((Γ i).adjoint v) = 0) ∧ Q (H.adjoint v) = 0 := by
    have hbal : H (Q v) + Q (H.adjoint v) + ρ • Q v =
        P v + ∑ i, Γ i (Q ((Γ i).adjoint v)) := by
      simpa only [H, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
        LinearMap.sum_apply] using LinearMap.congr_fun hbalance v
    have hz := congrArg (fun z => inner ℝ z v) hbal
    have hcross : inner ℝ (Q (H.adjoint v)) v = 0 := by
      rw [hQ.isSymmetric, hv, inner_zero_right]
    have hgi (i : ι) : inner ℝ (Γ i (Q ((Γ i).adjoint v))) v =
        inner ℝ (Q ((Γ i).adjoint v)) ((Γ i).adjoint v) :=
      (LinearMap.adjoint_inner_right (Γ i) _ v).symm
    simp only [hv, map_zero, add_zero, zero_add, smul_zero,
      inner_add_left, sum_inner, hcross, hgi] at hz
    have hp0 := hP.inner_nonneg_left v
    have hg0 : ∀ i, 0 ≤ inner ℝ (Q ((Γ i).adjoint v)) ((Γ i).adjoint v) :=
      fun i => hQ.inner_nonneg_left _
    have hsum0 := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => hg0 i)
    have hpz : inner ℝ (P v) v = 0 := by linarith
    have hpv := (positive_quadratic_zero_iff P hP v).mp hpz
    have hgv : ∀ i, Q ((Γ i).adjoint v) = 0 := by
      intro i
      apply (positive_quadratic_zero_iff Q hQ _).mp
      have hle := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hg0 j)
        (Finset.mem_univ i)
      linarith [hg0 i]
    refine ⟨hpv, hgv, ?_⟩
    simpa [hv, hpv, hgv] using hbal
  refine ⟨Γ, ?_⟩
  intro x hx
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact maps_range_of_adjoint_preserves_kernel Q (Γ i) hQ
      (fun v hv => (hker v hv).2.1 i) x hx
  · obtain ⟨y, rfl⟩ := hx
    have h := LinearMap.congr_fun hinput y
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sum_apply,
      LinearMap.zero_apply] using h
  · have h := maps_range_of_adjoint_preserves_kernel Q H hQ
      (fun v hv => (hker v hv).2.2) x hx
    simpa only [H, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply] using h

/-- A zero stabilized flag excludes every nonzero positive certificate of
the displayed dual form, for every real rate. -/
theorem zero_flag_excludes_dual_certificate
    (s : AdjointCoefficients (𝕜 := ℝ) (E := E) (U := U) (ι := ι))
    (hflag : s.flag (finrank ℝ E) = ⊥)
    (Q P : E →ₗ[ℝ] E) (Γ : ι → E →ₗ[ℝ] E) (ρ : ℝ)
    (hQ : Q.IsPositive) (hP : P.IsPositive)
    (hbalance :
      (s.A + ∑ i, (s.C i).comp (Γ i)).comp Q +
        Q.comp (s.A + ∑ i, (s.C i).comp (Γ i)).adjoint + ρ • Q =
          P + ∑ i, ((Γ i).comp Q).comp (Γ i).adjoint)
    (hinput : (s.B + ∑ i, (s.D i).comp (Γ i)).comp Q = 0) : Q = 0 := by
  have hs := dual_identity_invariant_selectors s Q P Γ ρ hQ hP hbalance hinput
  have hr := s.fixed_le_flag (s.fixed_of_selectors hs) (finrank ℝ E)
  rw [hflag] at hr
  exact LinearMap.range_eq_bot.mp (le_antisymm hr bot_le)

end LinearStochastic.ConeCertificate
