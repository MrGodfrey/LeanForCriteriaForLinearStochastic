import LinearStochastic.ConeCertificate

/-!
# Singular positive block factorization

The off-diagonal factor is constructed by quotienting by `ker Q` and then
extending from `range Q`. No inverse of the possibly singular `Q` is used.
-/
noncomputable section
namespace LinearStochastic.PositiveBlock

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Vanishing on a kernel gives an actual globally defined linear factor. -/
theorem factor_of_kernel_le (Q : E →ₗ[ℝ] E) (S : E →ₗ[ℝ] F)
    (h : Q.ker ≤ S.ker) : ∃ Γ : E →ₗ[ℝ] F, Γ.comp Q = S := by
  let g := (Q.ker.liftQ S h).comp Q.quotKerEquivRange.symm.toLinearMap
  obtain ⟨Γ, hΓ⟩ := g.exists_extend
  refine ⟨Γ, ?_⟩
  ext x
  change Γ (Q x) = S x
  have hx := LinearMap.congr_fun hΓ ⟨Q x, ⟨x, rfl⟩⟩
  simp only [g, LinearMap.comp_apply, Submodule.subtype_apply,
    LinearEquiv.coe_coe] at hx
  rw [Q.quotKerEquivRange_symm_apply_image x ⟨x, rfl⟩] at hx
  simpa only [Submodule.liftQ_apply, Submodule.mkQ_apply] using hx

/-- Positivity of the actual two-by-two quadratic form forces the
off-diagonal block to annihilate the kernel of the first diagonal block. -/
theorem positive_block_kernel_le (Q : E →ₗ[ℝ] E) (S : E →ₗ[ℝ] F)
    (R : F →ₗ[ℝ] F)
    (hblock : ∀ x y, 0 ≤ inner ℝ (Q x) x + 2 * inner ℝ (S x) y + inner ℝ (R y) y) :
    Q.ker ≤ S.ker := by
  intro x hx
  change Q x = 0 at hx
  change S x = 0
  apply ext_inner_right ℝ
  intro y
  simp only [inner_zero_left]
  have hlin : ∀ t : ℝ, 0 ≤ 0 * (t * t) + (2 * inner ℝ (S x) y) * t +
      inner ℝ (R y) y := by
    intro t
    have h := hblock (t • x) y
    simp only [map_smul, hx, smul_zero, inner_zero_left, zero_add,
      real_inner_smul_left] at h
    nlinarith
  have hd := discrim_le_zero hlin
  simp only [discrim, mul_zero, zero_mul, sub_zero] at hd
  nlinarith [sq_nonneg (inner ℝ (S x) y)]

/-- Singular Schur factorization: `S=ΓQ` and the residual
`R−ΓQΓ†` is positive. All witness construction is proved. -/
theorem positive_block_factorization (Q : E →ₗ[ℝ] E) (S : E →ₗ[ℝ] F)
    (R : F →ₗ[ℝ] F) (hQ : Q.IsPositive) (hR : R.IsSymmetric)
    (hblock : ∀ x y, 0 ≤ inner ℝ (Q x) x + 2 * inner ℝ (S x) y + inner ℝ (R y) y) :
    ∃ Γ : E →ₗ[ℝ] F, Γ.comp Q = S ∧
      (R - (Γ.comp Q).comp Γ.adjoint).IsPositive := by
  obtain ⟨Γ, hΓ⟩ := factor_of_kernel_le Q S (positive_block_kernel_le Q S R hblock)
  refine ⟨Γ, hΓ, ?_⟩
  rw [LinearMap.isPositive_iff]
  refine ⟨hR.sub (hQ.conj_adjoint Γ).isSymmetric, ?_⟩
  intro y
  have hs (x : E) : S x = Γ (Q x) := (LinearMap.congr_fun hΓ x).symm
  have hi : inner ℝ (Γ (Q (Γ.adjoint y))) y = inner ℝ (Q (Γ.adjoint y)) (Γ.adjoint y) :=
    (LinearMap.adjoint_inner_right Γ _ y).symm
  have hb := hblock (-Γ.adjoint y) y
  simp only [hs, map_neg, inner_neg_left, inner_neg_right, neg_neg, hi] at hb
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, inner_sub_left, hi]
  linarith

end LinearStochastic.PositiveBlock
