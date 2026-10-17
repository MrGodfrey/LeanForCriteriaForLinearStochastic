module

public import LinearStochastic.AlgebraRank

@[expose] public section

/-!
# Drift inputs in the joint diffusion kernel

The maps `B : U → E` and `D : U → W` here are forward maps, unlike the
transposed maps in `AdjointCoefficients`. In the paper `W` is the direct sum
of all diffusion channels. No controllability assertion is assumed here.
-/

noncomputable section
namespace LinearStochastic.InputStructure
open Module
open scoped BigOperators

variable {E U W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- The first feasibility space is exactly the annihilator of drift inputs
whose joint diffusion vanishes. -/
theorem feasible_adjoint_eq_orthogonal (B : U →ₗ[ℝ] E) (D : U →ₗ[ℝ] W) :
    feasibleSpace B.adjoint D.adjoint = (D.ker.map B)ᗮ := by
  rw [feasibleSpace, ← D.orthogonal_ker]
  ext v
  simp only [Submodule.mem_comap, Submodule.mem_orthogonal, Submodule.mem_map]
  constructor
  · intro h y hy
    obtain ⟨u, hu, rfl⟩ := hy
    rw [← LinearMap.adjoint_inner_right]
    exact h u hu
  · intro h u hu
    rw [LinearMap.adjoint_inner_right]
    exact h (B u) ⟨u, hu, rfl⟩

/-- Vanishing drift on the diffusion kernel makes the first feasibility
condition impose no restriction. -/
theorem feasible_adjoint_eq_top_iff (B : U →ₗ[ℝ] E) (D : U →ₗ[ℝ] W) :
    feasibleSpace B.adjoint D.adjoint = ⊤ ↔ D.ker.map B = ⊥ := by
  rw [feasible_adjoint_eq_orthogonal, Submodule.orthogonal_eq_top_iff]

/-- A surjective diffusion map plus a nonzero drift input in its kernel
requires at least one more input dimension than diffusion dimensions. -/
theorem input_dimension_lower_bound (B : U →ₗ[ℝ] E) (D : U →ₗ[ℝ] W)
    (hD : Function.Surjective D) (hB : D.ker.map B ≠ ⊥) :
    finrank ℝ W + 1 ≤ finrank ℝ U := by
  have hk : D.ker ≠ ⊥ := by
    intro h
    apply hB
    simp [h]
  have hpos : 0 < finrank ℝ D.ker := by
    exact Nat.pos_of_ne_zero (fun h => hk (Submodule.finrank_eq_zero.mp h))
  have hdim := D.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hD, finrank_top] at hdim
  omega

/-- Every right inverse yields the algebraic projection onto the diffusion
kernel used in the reduced exact-controllability matrices. -/
theorem range_id_sub_rightInverse_comp (D : U →ₗ[ℝ] W) (J : W →ₗ[ℝ] U)
    (hJ : D.comp J = LinearMap.id) :
    (LinearMap.id - J.comp D).range = D.ker := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    change D (v - J (D v)) = 0
    have h := LinearMap.congr_fun hJ (D v)
    change D (J (D v)) = D v at h
    simp [h]
  · intro hu
    refine ⟨u, ?_⟩
    change u - J (D u) = u
    change D u = 0 at hu
    simp [hu]

/-- The corresponding effective drift has exactly the image `B (ker D)`. -/
theorem effective_drift_range (B : U →ₗ[ℝ] E) (D : U →ₗ[ℝ] W)
    (J : W →ₗ[ℝ] U) (hJ : D.comp J = LinearMap.id) :
    (B.comp (LinearMap.id - J.comp D)).range = D.ker.map B := by
  rw [LinearMap.range_comp, range_id_sub_rightInverse_comp D J hJ]

/-- The same projection is idempotent; this does not by itself assert
orthogonality for an arbitrary right inverse. -/
theorem id_sub_rightInverse_comp_idempotent (D : U →ₗ[ℝ] W)
    (J : W →ₗ[ℝ] U) (hJ : D.comp J = LinearMap.id) :
    (LinearMap.id - J.comp D).comp (LinearMap.id - J.comp D) =
      LinearMap.id - J.comp D := by
  ext u
  have h := LinearMap.congr_fun hJ (D u)
  change D (J (D u)) = D u at h
  change (u - J (D u)) - J (D (u - J (D u))) = u - J (D u)
  simp [h]

/-- The joint diffusion Gram operator is invertible when the diffusion is onto. -/
def diffusionGramEquiv (D : U →ₗ[ℝ] W) (hD : Function.Surjective D) : W ≃ₗ[ℝ] W :=
  LinearEquiv.ofBijective (D.comp D.adjoint) (by
    constructor
    · rw [← LinearMap.ker_eq_bot, D.ker_self_comp_adjoint,
        ← D.orthogonal_range, LinearMap.range_eq_top.mpr hD,
        Submodule.top_orthogonal_eq_bot]
    · rw [← LinearMap.range_eq_top, D.range_self_comp_adjoint,
        LinearMap.range_eq_top.mpr hD])

/-- `J=D†(DD†)⁻¹`, with the inverse constructed from proved bijectivity. -/
def canonicalRightInverse (D : U →ₗ[ℝ] W) (hD : Function.Surjective D) : W →ₗ[ℝ] U :=
  D.adjoint.comp (diffusionGramEquiv D hD).symm.toLinearMap

theorem canonicalRightInverse_right_inverse (D : U →ₗ[ℝ] W)
    (hD : Function.Surjective D) :
    D.comp (canonicalRightInverse D hD) = LinearMap.id := by
  ext w
  exact (diffusionGramEquiv D hD).apply_symm_apply w

/-- The manuscript's canonical `I−JD` really is an orthogonal projection,
not merely an algebraic projection from an arbitrary right inverse. -/
theorem canonical_kernel_projection (D : U →ₗ[ℝ] W) (hD : Function.Surjective D) :
    let J := canonicalRightInverse D hD
    (LinearMap.id - J.comp D).IsSymmetric ∧
      (LinearMap.id - J.comp D).comp (LinearMap.id - J.comp D) = LinearMap.id - J.comp D ∧
      (LinearMap.id - J.comp D).range = D.ker := by
  let J := canonicalRightInverse D hD
  have hr : D.comp J = LinearMap.id := canonicalRightInverse_right_inverse D hD
  have hg : (diffusionGramEquiv D hD).toLinearMap.IsPositive :=
    LinearMap.isPositive_self_comp_adjoint D
  have hinv := hg.toLinearMap_symm
  have hproj : (J.comp D).IsSymmetric := by
    simpa only [J, canonicalRightInverse, LinearMap.comp_assoc] using
      (hinv.adjoint_conj D).isSymmetric
  exact ⟨LinearMap.IsSymmetric.id.sub hproj,
    id_sub_rightInverse_comp_idempotent D J hr, range_id_sub_rightInverse_comp D J hr⟩

/-- The complementary canonical projection `JD` has exactly the adjoint
diffusion range, equivalently the orthogonal complement of `ker D`. -/
theorem canonical_diffusion_projection (D : U →ₗ[ℝ] W) (hD : Function.Surjective D) :
    let J := canonicalRightInverse D hD
    (J.comp D).IsSymmetric ∧ (J.comp D).comp (J.comp D) = J.comp D ∧
      (J.comp D).range = D.adjoint.range ∧ (J.comp D).range = D.kerᗮ := by
  let J := canonicalRightInverse D hD
  have hr : D.comp J = LinearMap.id := canonicalRightInverse_right_inverse D hD
  have hsym : (J.comp D).IsSymmetric := by
    have hs := LinearMap.IsSymmetric.id.sub (canonical_kernel_projection D hD).1
    simpa only [sub_sub_cancel] using hs
  have hidem : (J.comp D).comp (J.comp D) = J.comp D := by
    ext u
    have h := LinearMap.congr_fun hr (D u)
    change D (J (D u)) = D u at h
    change J (D (J (D u))) = J (D u)
    rw [h]
  have hrange : (J.comp D).range = D.adjoint.range := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hD, Submodule.map_top]
    change (D.adjoint.comp (diffusionGramEquiv D hD).symm.toLinearMap).range = _
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  exact ⟨hsym, hidem, hrange, hrange.trans D.orthogonal_ker.symm⟩

section Channels
variable {ι : Type*} [Fintype ι]

/-- The actual joint forward diffusion map, with all channels retained. -/
def jointDiffusion (D : ι → U →ₗ[ℝ] E) : U →ₗ[ℝ] PiLp 2 (fun _ : ι => E) :=
  (WithLp.linearEquiv 2 ℝ (ι → E)).symm.toLinearMap.comp (LinearMap.pi D)

/-- Adjoint of the stacked diffusion is the sum of the channel adjoints. -/
theorem jointDiffusion_adjoint_apply (D : ι → U →ₗ[ℝ] E)
    (w : PiLp 2 (fun _ : ι => E)) :
    (jointDiffusion D).adjoint w = ∑ i, (D i).adjoint (w i) := by
  apply ext_inner_right ℝ
  intro u
  rw [LinearMap.adjoint_inner_left, PiLp.inner_apply, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.adjoint_inner_left]
  rfl

/-- Forward state/input coefficients converted to the paper's adjoint flag. -/
def fromForward (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (C : ι → E →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E) :
    AdjointCoefficients (𝕜 := ℝ) (E := E) (U := U) (ι := ι) where
  A := A.adjoint
  B := B.adjoint
  C := fun i => (C i).adjoint
  D := fun i => (D i).adjoint

/-- The first flag iterate, proved for the actual multichannel recursion. -/
theorem flag_one_eq_orthogonal (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (C : ι → E →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E) :
    (fromForward A B C D).flag 1 = ((jointDiffusion D).ker.map B)ᗮ := by
  rw [← feasible_adjoint_eq_orthogonal B (jointDiffusion D)]
  ext v
  rw [mem_feasibleSpace]
  change (v ∈ (⊤ : Submodule ℝ E) ∧ ∃ w : ι → E,
    (∀ i, w i ∈ (⊤ : Submodule ℝ E)) ∧
    B.adjoint v + ∑ i, (D i).adjoint (w i) = 0 ∧
    A.adjoint v + ∑ i, (C i).adjoint (w i) ∈ (⊤ : Submodule ℝ E)) ↔ _
  simp only [Submodule.mem_top, true_and, and_true, implies_true]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨WithLp.toLp 2 w, ?_⟩
    rwa [jointDiffusion_adjoint_apply]
  · rintro ⟨w, hw⟩
    rw [jointDiffusion_adjoint_apply] at hw
    exact ⟨fun i => w i, hw⟩

/-- If no diffusion-free input acts through the drift, every iterate remains
the whole state space, not merely the first iterate. -/
theorem flag_eq_top_of_drift_kernel_zero (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (C : ι → E →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E)
    (h : (jointDiffusion D).ker.map B = ⊥) (k : ℕ) :
    (fromForward A B C D).flag k = ⊤ := by
  have hfirst : (fromForward A B C D).flag 1 = (fromForward A B C D).flag 0 := by
    rw [flag_one_eq_orthogonal, h, Submodule.bot_orthogonal_eq_top,
      AdjointCoefficients.flag_zero]
  simpa using (fromForward A B C D).stationary_of_step_eq hfirst k

/-- For a nonzero state space, a zero stabilized flag forces a nonzero
diffusion-free drift input. -/
theorem drift_kernel_ne_zero_of_flag_bot [Nontrivial E]
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E)
    (C : ι → E →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E) (k : ℕ)
    (h : (fromForward A B C D).flag k = ⊥) :
    (jointDiffusion D).ker.map B ≠ ⊥ := by
  intro hz
  have ht := flag_eq_top_of_drift_kernel_zero A B C D hz k
  exact top_ne_bot (ht.symm.trans h)

end Channels

end LinearStochastic.InputStructure
