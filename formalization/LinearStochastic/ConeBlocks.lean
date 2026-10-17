module

public import LinearStochastic.PositiveBlock

@[expose] public section
noncomputable section
namespace LinearStochastic.ConeBlocks
open scoped BigOperators
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

abbrev BlockSpace (E ι : Type*) [NormedAddCommGroup E] := PiLp 2 (fun _ : ι => E)

def inject (i : ι) : E →ₗ[ℝ] BlockSpace E ι :=
  (WithLp.linearEquiv 2 ℝ (ι → E)).symm.toLinearMap.comp (LinearMap.single ℝ (fun _ : ι => E) i)

def project (i : ι) : BlockSpace E ι →ₗ[ℝ] E := PiLp.projₗ (𝕜 := ℝ) (β := fun _ : ι => E) 2 i

@[simp] theorem inject_apply (i : ι) (x : E) : inject i x = PiLp.single 2 i x := rfl
@[simp] theorem project_apply (i : ι) (x : BlockSpace E ι) : project i x = x i := rfl

theorem inject_adjoint (i : ι) : (inject (E := E) i).adjoint = project i := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [LinearMap.adjoint_inner_left]
  simp [inject, project, PiLp.inner_apply, real_inner_comm, apply_ite]

theorem sum_inject_project (x : BlockSpace E ι) : ∑ i, inject i (project i x) = x := by
  ext j
  simp [inject, project]

def block (Z : BlockSpace E ι →ₗ[ℝ] BlockSpace E ι) (i j : ι) : E →ₗ[ℝ] E :=
  (project i).comp (Z.comp (inject j))

theorem block_diagonal_positive (Z : BlockSpace E ι →ₗ[ℝ] BlockSpace E ι)
    (hZ : Z.IsPositive) (i : ι) : (block Z i i).IsPositive := by
  rw [block, ← inject_adjoint]
  exact hZ.adjoint_conj (inject i)

theorem positive_block_zero_column (Z : BlockSpace E ι →ₗ[ℝ] BlockSpace E ι)
    (hZ : Z.IsPositive) (i : ι) (hz : block Z i i = 0) : Z.comp (inject i) = 0 := by
  apply LinearMap.ext
  intro x
  apply (ConeCertificate.positive_quadratic_zero_iff Z hZ (inject i x)).mp
  have h := LinearMap.congr_fun hz x
  change project i (Z (inject i x)) = 0 at h
  have hi : inner ℝ (Z (inject i x)) (inject i x) =
      inner ℝ (project i (Z (inject i x))) x := by
    rw [← inject_adjoint, LinearMap.adjoint_inner_left]
  rw [hi, h, inner_zero_left]

theorem positive_eq_zero_of_diagonal_blocks_zero
    (Z : BlockSpace E ι →ₗ[ℝ] BlockSpace E ι) (hZ : Z.IsPositive)
    (hz : ∀ i, block Z i i = 0) : Z = 0 := by
  apply LinearMap.ext
  intro x
  conv_lhs => rw [← sum_inject_project x]
  rw [map_sum]
  have hh (i : ι) : Z (inject i (project i x)) = 0 :=
    LinearMap.congr_fun (positive_block_zero_column Z hZ i (hz i)) (project i x)
  simp only [hh, Finset.sum_const_zero, LinearMap.zero_apply]

end LinearStochastic.ConeBlocks

namespace LinearStochastic.ConeBlocks
open scoped BigOperators
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι] [DecidableEq ι]

theorem project_adjoint (i : ι) : (project (E := E) i).adjoint = inject i := by
  rw [← inject_adjoint, LinearMap.adjoint_adjoint]

theorem block_adjoint (Z : BlockSpace E ι →ₗ[ℝ] BlockSpace E ι)
    (hZ : Z.IsSymmetric) (i j : ι) : (block Z i j).adjoint = block Z j i := by
  simp [block, LinearMap.adjoint_comp, inject_adjoint, project_adjoint,
    hZ.adjoint_eq, LinearMap.comp_assoc]

theorem block_inner (Z : BlockSpace E ι →ₗ[ℝ] BlockSpace E ι)
    (i j : ι) (x y : E) :
    inner ℝ (block Z i j x) y = inner ℝ (Z (inject j x)) (inject i y) := by
  change inner ℝ (project i (Z (inject j x))) y = _
  rw [← inject_adjoint, LinearMap.adjoint_inner_left]

theorem two_block_positive (Z : BlockSpace E ι →ₗ[ℝ] BlockSpace E ι)
    (hZ : Z.IsPositive) (i j : ι) (x y : E) :
    0 ≤ inner ℝ (block Z i i x) x + 2 * inner ℝ (block Z j i x) y +
      inner ℝ (block Z j j y) y := by
  have h := hZ.inner_nonneg_left (inject i x + inject j y)
  have hcross : inner ℝ (Z (inject j y)) (inject i x) =
      inner ℝ (Z (inject i x)) (inject j y) := by
    rw [hZ.isSymmetric, real_inner_comm]
  simp only [map_add, inner_add_left, inner_add_right, hcross] at h
  simp only [block_inner]
  linarith

theorem block_factorization (Z : BlockSpace E ι →ₗ[ℝ] BlockSpace E ι)
    (hZ : Z.IsPositive) (i j : ι) :
    ∃ Γ : E →ₗ[ℝ] E, Γ.comp (block Z i i) = block Z j i ∧
      (block Z j j - (Γ.comp (block Z i i)).comp Γ.adjoint).IsPositive := by
  exact PositiveBlock.positive_block_factorization _ _ _
    (block_diagonal_positive Z hZ i) (block_diagonal_positive Z hZ j).isSymmetric
    (two_block_positive Z hZ i j)

theorem positive_sum (R : ι → E →ₗ[ℝ] E) (hR : ∀ i, (R i).IsPositive) :
    (∑ i, R i).IsPositive := by
  exact Finset.sum_induction R LinearMap.IsPositive (fun _ _ ha hb => ha.add hb) LinearMap.isPositive_zero
    (fun i _ => hR i)

theorem positive_summands_zero (R : ι → E →ₗ[ℝ] E) (hR : ∀ i, (R i).IsPositive)
    (hs : ∑ i, R i = 0) : ∀ i, R i = 0 := by
  intro i
  apply LinearMap.ext
  intro x
  apply (ConeCertificate.positive_quadratic_zero_iff (R i) (hR i) x).mp
  have hz := congrArg (fun T : E →ₗ[ℝ] E => inner ℝ (T x) x) hs
  simp only [LinearMap.sum_apply, sum_inner, LinearMap.zero_apply, inner_zero_left] at hz
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hR j).inner_nonneg_left x)).mp hz i
    (Finset.mem_univ i)

end LinearStochastic.ConeBlocks

namespace LinearStochastic.ConeBlocks
open scoped BigOperators
variable {E U ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [AddCommGroup U] [Module ℝ U] [Fintype ι] [DecidableEq ι]

/-- The top-left block of a nonzero positive dual certificate cannot vanish
when its state coefficient identity is satisfied. -/
theorem head_nonzero_of_balance
    (Z : BlockSpace E (Option ι) →ₗ[ℝ] BlockSpace E (Option ι))
    (hZ : Z.IsPositive) (hn : Z ≠ 0) (A : E →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E) (ρ : ℝ)
    (hb : A.comp (block Z none none) + (block Z none none).comp A.adjoint +
      ρ • block Z none none + ∑ i, ((C i).comp (block Z (some i) none) +
        (block Z (some i) none).adjoint.comp (C i).adjoint) =
      ∑ i, block Z (some i) (some i)) : block Z none none ≠ 0 := by
  intro hQ
  have hcol := positive_block_zero_column Z hZ none hQ
  have hS (i : ι) : block Z (some i) none = 0 := by
    apply LinearMap.ext
    intro x
    have hz : Z (inject none x) = 0 := LinearMap.congr_fun hcol x
    change project (some i) (Z (inject none x)) = 0
    rw [hz, map_zero]
  have hR : ∑ i, block Z (some i) (some i) = 0 := by
    simpa [hQ, hS] using hb.symm
  have hRi := positive_summands_zero (fun i : ι => block Z (some i) (some i))
    (fun i => block_diagonal_positive Z hZ (some i)) hR
  apply hn
  apply positive_eq_zero_of_diagonal_blocks_zero Z hZ
  intro i
  cases i with
  | none => exact hQ
  | some j => exact hRi j

/-- A concrete nonzero positive block operator satisfying the two LMI dual
coefficient identities forces a nonzero obstruction. The selectors and
positive residual are constructed, including when the head block is singular. -/
theorem zero_flag_excludes_block_certificate
    (s : AdjointCoefficients (𝕜 := ℝ) (E := E) (U := U) (ι := ι))
    (hflag : s.flag (Module.finrank ℝ E) = ⊥)
    (Z : BlockSpace E (Option ι) →ₗ[ℝ] BlockSpace E (Option ι))
    (hZ : Z.IsPositive) (ρ : ℝ)
    (hb : s.A.comp (block Z none none) + (block Z none none).comp s.A.adjoint +
      ρ • block Z none none + ∑ i, ((s.C i).comp (block Z (some i) none) +
        (block Z (some i) none).adjoint.comp (s.C i).adjoint) =
      ∑ i, block Z (some i) (some i))
    (hi : s.B.comp (block Z none none) +
      ∑ i, (s.D i).comp (block Z (some i) none) = 0) : Z = 0 := by
  by_contra hn
  let Q := block Z none none
  have hQ : Q.IsPositive := block_diagonal_positive Z hZ none
  have hQn : Q ≠ 0 := head_nonzero_of_balance Z hZ hn s.A s.C ρ hb
  have hf (i : ι) := block_factorization Z hZ none (some i)
  choose Γ hΓ hres using hf
  let P := ∑ i, (block Z (some i) (some i) - (Γ i |>.comp Q).comp (Γ i).adjoint)
  have hP : P.IsPositive := positive_sum _ hres
  apply hQn
  apply ConeCertificate.zero_flag_excludes_dual_certificate s hflag Q P Γ ρ hQ hP
  · have hΓadj (i : ι) : Q.comp (Γ i).adjoint = (block Z (some i) none).adjoint := by
      rw [← hΓ i, LinearMap.adjoint_comp, hQ.adjoint_eq]
    have hleft :
        (s.A + ∑ i, (s.C i).comp (Γ i)).comp Q +
          Q.comp (s.A + ∑ i, (s.C i).comp (Γ i)).adjoint + ρ • Q =
        s.A.comp Q + Q.comp s.A.adjoint + ρ • Q +
          ∑ i, ((s.C i).comp (block Z (some i) none) +
            (block Z (some i) none).adjoint.comp (s.C i).adjoint) := by
      apply LinearMap.ext
      intro x
      have hg (i : ι) (y : E) : Γ i (Q y) = block Z (some i) none y := LinearMap.congr_fun (hΓ i) y
      have hga (i : ι) (y : E) : Q ((Γ i).adjoint y) = (block Z (some i) none).adjoint y :=
        LinearMap.congr_fun (hΓadj i) y
      simp only [map_add, map_sum, LinearMap.adjoint_comp, LinearMap.comp_apply,
        LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, hg, hga,
        Finset.sum_add_distrib]
      abel
    rw [hleft, hb]
    simp only [P, Finset.sum_sub_distrib]
    abel
  · apply LinearMap.ext
    intro x
    have hg (i : ι) : Γ i (Q x) = block Z (some i) none x := LinearMap.congr_fun (hΓ i) x
    have hh := LinearMap.congr_fun hi x
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply,
      LinearMap.zero_apply, hg] using hh

end LinearStochastic.ConeBlocks
