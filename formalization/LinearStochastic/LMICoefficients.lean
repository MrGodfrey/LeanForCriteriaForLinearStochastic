module

public import LinearStochastic.ConeBlocks
public import LinearStochastic.PositiveDual
public import LinearStochastic.InputStructure

@[expose] public section
noncomputable section
namespace LinearStochastic.LMICoefficients
open scoped BigOperators
open ConeBlocks
variable {E U ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [Fintype ι] [DecidableEq ι]

/-- Put a linear map in the indicated block, all other blocks being zero. -/
def liftBlock (i j : ι) (T : E →ₗ[ℝ] E) : BlockSpace E ι →ₗ[ℝ] BlockSpace E ι :=
  (inject i).comp (T.comp (project j))

theorem liftBlock_adjoint (i j : ι) (T : E →ₗ[ℝ] E) :
    (liftBlock i j T).adjoint = liftBlock j i T.adjoint := by
  simp [liftBlock, LinearMap.adjoint_comp, inject_adjoint, project_adjoint,
    LinearMap.comp_assoc]

theorem trace_liftBlock (Z : BlockSpace E ι →ₗ[ℝ] BlockSpace E ι)
    (i j : ι) (T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ (BlockSpace E ι) (Z.comp (liftBlock i j T)) =
      LinearMap.trace ℝ E ((block Z j i).comp T) := by
  unfold liftBlock block
  simp only [← LinearMap.comp_assoc]
  rw [LinearMap.trace_comp_comm']
  congr 1

/-- The actual manuscript LMI, indexed by a state block and all noise blocks. -/
def lmi (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U) :
    BlockSpace E (Option ι) →ₗ[ℝ] BlockSpace E (Option ι) :=
  liftBlock none none (A.comp P + P.comp A.adjoint + B.comp K + K.adjoint.comp B.adjoint + ρ • P) +
  ∑ i, (liftBlock (some i) none ((C i).comp P + (D i).comp K) +
    liftBlock none (some i) (((C i).comp P + (D i).comp K).adjoint) -
    liftBlock (some i) (some i) P)

theorem liftBlock_add (i j : ι) (S T : E →ₗ[ℝ] E) :
    liftBlock i j (S + T) = liftBlock i j S + liftBlock i j T := by
  apply LinearMap.ext
  intro x
  simp only [liftBlock, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]

theorem liftBlock_smul (i j : ι) (c : ℝ) (T : E →ₗ[ℝ] E) :
    liftBlock i j (c • T) = c • liftBlock i j T := by
  apply LinearMap.ext
  intro x
  simp only [liftBlock, LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul]

theorem lmi_symmetric (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (hP : P.IsSymmetric)
    (K : E →ₗ[ℝ] U) : (lmi A B C D ρ P K).IsSymmetric := by
  apply (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr
  rw [LinearMap.isSelfAdjoint_iff']
  simp only [lmi, map_add, map_sum, map_sub, map_smul, liftBlock_adjoint,
    LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, hP.adjoint_eq]
  congr 1
  · congr 1
    abel
  · apply Finset.sum_congr rfl
    intro i _
    abel

end LinearStochastic.LMICoefficients

namespace LinearStochastic.LMICoefficients
open scoped BigOperators
open ConeBlocks
variable {E U ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [Fintype ι] [DecidableEq ι]

theorem trace_adjoint (T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E T.adjoint = LinearMap.trace ℝ E T := by
  rw [LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℝ E),
    LinearMap.trace_eq_sum_inner T (stdOrthonormalBasis ℝ E)]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.adjoint_inner_right, real_inner_comm]

theorem trace_comp_adjoint (S T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E (S.comp T.adjoint) =
      LinearMap.trace ℝ E (S.adjoint.comp T) := by
  rw [← trace_adjoint (S.comp T.adjoint), LinearMap.adjoint_comp,
    LinearMap.adjoint_adjoint, LinearMap.trace_comp_comm']

theorem trace_comp_add (Q S T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E (Q.comp (S+T)) =
      LinearMap.trace ℝ E (Q.comp S) + LinearMap.trace ℝ E (Q.comp T) := by
  rw [LinearMap.comp_add, map_add]

theorem trace_comp_sub (Q S T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E (Q.comp (S-T)) =
      LinearMap.trace ℝ E (Q.comp S) - LinearMap.trace ℝ E (Q.comp T) := by
  rw [LinearMap.comp_sub, map_sub]

theorem trace_comp_sum (Q : E →ₗ[ℝ] E) (T : ι → E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E (Q.comp (∑ i, T i)) =
      ∑ i, LinearMap.trace ℝ E (Q.comp (T i)) := by
  have hh : Q.comp (∑ i, T i) = ∑ i, Q.comp (T i) := by
    ext x
    simp
  rw [hh, map_sum]

/-- The block trace expansion, with both off-diagonal pieces accounted for. -/
theorem trace_lmi_blocks
    (Z : BlockSpace E (Option ι) →ₗ[ℝ] BlockSpace E (Option ι))
    (hZ : Z.IsSymmetric)
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U) :
    LinearMap.trace ℝ _ (Z.comp (lmi A B C D ρ P K)) =
      LinearMap.trace ℝ E ((block Z none none).comp
        (A.comp P + P.comp A.adjoint + B.comp K + K.adjoint.comp B.adjoint + ρ • P)) +
      ∑ i, (2 * LinearMap.trace ℝ E ((block Z (some i) none).adjoint.comp
        ((C i).comp P + (D i).comp K)) -
        LinearMap.trace ℝ E ((block Z (some i) (some i)).comp P)) := by
  simp only [lmi, trace_comp_add, trace_comp_sum, trace_comp_sub, trace_liftBlock]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← block_adjoint Z hZ (some i) none, trace_comp_adjoint]
  simp only [trace_comp_add]
  ring

end LinearStochastic.LMICoefficients

namespace LinearStochastic.LMICoefficients
open scoped BigOperators
open ConeBlocks
variable {E U ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [Fintype ι] [DecidableEq ι]
variable (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ)

theorem lmi_add (P Q : E →ₗ[ℝ] E) (K L : E →ₗ[ℝ] U) :
    lmi A B C D ρ (P+Q) (K+L) = lmi A B C D ρ P K + lmi A B C D ρ Q L := by
  apply LinearMap.ext
  intro x
  simp only [lmi, liftBlock, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.adjoint_comp, map_add, map_sub, map_sum, map_smul, smul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

theorem lmi_smul (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U) (c : ℝ) :
    lmi A B C D ρ (c • P) (c • K) = c • lmi A B C D ρ P K := by
  apply LinearMap.ext
  intro x
  simp only [lmi, liftBlock, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.adjoint_comp, map_add, map_sub, map_sum, map_smul, smul_add,
    smul_sub, Finset.smul_sum, smul_comm ρ c]

/-- The actual LMI as a linear map into the space of symmetric operators. -/
def lmiMap : (selfAdjoint (E →L[ℝ] E) × (E →ₗ[ℝ] U)) →ₗ[ℝ]
    selfAdjoint (BlockSpace E (Option ι) →L[ℝ] BlockSpace E (Option ι)) where
  toFun p := (lmi_symmetric A B C D ρ p.1.val.toLinearMap
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp p.1.property) p.2).toSelfAdjoint
  map_add' p q := by
    apply Subtype.ext
    apply ContinuousLinearMap.coe_injective
    exact lmi_add A B C D ρ p.1.val.toLinearMap q.1.val.toLinearMap p.2 q.2
  map_smul' c p := by
    apply Subtype.ext
    apply ContinuousLinearMap.coe_injective
    exact lmi_smul A B C D ρ p.1.val.toLinearMap p.2 c

end LinearStochastic.LMICoefficients

namespace LinearStochastic.LMICoefficients
open scoped BigOperators
open ConeBlocks
variable {E U ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [Fintype ι] [DecidableEq ι]

theorem trace_cycle_three (Q A P : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E (Q.comp (P.comp A)) = LinearMap.trace ℝ E ((A.comp Q).comp P) := by
  rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm']
  congr 1

theorem trace_symmetric_right (T P : E →ₗ[ℝ] E) (hP : P.IsSymmetric) :
    LinearMap.trace ℝ E (T.adjoint.comp P) = LinearMap.trace ℝ E (T.comp P) := by
  rw [← trace_adjoint (T.adjoint.comp P), LinearMap.adjoint_comp,
    hP.adjoint_eq, LinearMap.adjoint_adjoint, LinearMap.trace_comp_comm']

theorem trace_control_pair (Q : E →ₗ[ℝ] E) (hQ : Q.IsSymmetric)
    (B : U →ₗ[ℝ] E) (K : E →ₗ[ℝ] U) :
    LinearMap.trace ℝ E (Q.comp (K.adjoint.comp B.adjoint)) =
      LinearMap.trace ℝ E ((Q.comp B).comp K) := by
  rw [← trace_adjoint (Q.comp (K.adjoint.comp B.adjoint))]
  simp only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, hQ.adjoint_eq]
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]

/-- State coefficient obtained by varying the symmetric Lyapunov variable. -/
def stateCoefficient
    (Z : BlockSpace E (Option ι) →ₗ[ℝ] BlockSpace E (Option ι))
    (A : E →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E) (ρ : ℝ) : E →ₗ[ℝ] E :=
  A.adjoint.comp (block Z none none) + (block Z none none).comp A + ρ • block Z none none +
    ∑ i, ((C i).adjoint.comp (block Z (some i) none) +
      (block Z (some i) none).adjoint.comp (C i)) - ∑ i, block Z (some i) (some i)

/-- Input coefficient obtained by varying the full rectangular control variable. -/
def inputCoefficient
    (Z : BlockSpace E (Option ι) →ₗ[ℝ] BlockSpace E (Option ι))
    (B : U →ₗ[ℝ] E) (D : ι → U →ₗ[ℝ] E) : E →ₗ[ℝ] U :=
  B.adjoint.comp (block Z none none) + ∑ i, (D i).adjoint.comp (block Z (some i) none)

theorem trace_add_comp (Q S T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E ((Q+S).comp T) =
      LinearMap.trace ℝ E (Q.comp T) + LinearMap.trace ℝ E (S.comp T) := by
  rw [LinearMap.add_comp, map_add]

theorem trace_sub_comp (Q S T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E ((Q-S).comp T) =
      LinearMap.trace ℝ E (Q.comp T) - LinearMap.trace ℝ E (S.comp T) := by
  rw [LinearMap.sub_comp, map_sub]

theorem trace_sum_comp (Q : ι → E →ₗ[ℝ] E) (T : E →ₗ[ℝ] E) :
    LinearMap.trace ℝ E ((∑ i, Q i).comp T) =
      ∑ i, LinearMap.trace ℝ E ((Q i).comp T) := by
  have hh : (∑ i, Q i).comp T = ∑ i, (Q i).comp T := by
    ext x
    simp
  rw [hh, map_sum]

theorem stateCoefficient_symmetric
    (Z : BlockSpace E (Option ι) →ₗ[ℝ] BlockSpace E (Option ι))
    (hZ : Z.IsSymmetric) (A : E →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E) (ρ : ℝ) :
    (stateCoefficient Z A C ρ).IsSymmetric := by
  apply (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr
  rw [LinearMap.isSelfAdjoint_iff']
  simp only [stateCoefficient, map_add, map_sub, map_sum, map_smul,
    LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, block_adjoint Z hZ]
  simp only [Finset.sum_add_distrib]
  abel

end LinearStochastic.LMICoefficients

namespace LinearStochastic.LMICoefficients
open scoped BigOperators
open ConeBlocks
variable {E U ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [Fintype ι] [DecidableEq ι]

theorem trace_lmi_coefficients
    (Z : BlockSpace E (Option ι) →ₗ[ℝ] BlockSpace E (Option ι))
    (hZ : Z.IsSymmetric)
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (hP : P.IsSymmetric)
    (K : E →ₗ[ℝ] U) :
    LinearMap.trace ℝ _ (Z.comp (lmi A B C D ρ P K)) =
      LinearMap.trace ℝ E ((stateCoefficient Z A C ρ).comp P) +
        2 * LinearMap.trace ℝ E ((inputCoefficient Z B D).adjoint.comp K) := by
  let Q := block Z none none
  have hQ : Q.IsSymmetric := by
    apply (LinearMap.isSymmetric_iff_isSelfAdjoint _).mpr
    exact block_adjoint Z hZ none none
  have hI : (inputCoefficient Z B D).adjoint.comp K =
      (Q.comp B).comp K + ∑ i, ((block Z (some i) none).adjoint.comp (D i)).comp K := by
    apply LinearMap.ext
    intro x
    simp only [inputCoefficient, map_add, map_sum, LinearMap.adjoint_comp,
      LinearMap.adjoint_adjoint, block_adjoint Z hZ, LinearMap.comp_apply,
      LinearMap.add_apply, LinearMap.sum_apply, Q]
  have hC (i : ι) : LinearMap.trace ℝ E (((C i).adjoint.comp (block Z (some i) none)).comp P) =
      LinearMap.trace ℝ E (((block Z (some i) none).adjoint.comp (C i)).comp P) := by
    simpa only [LinearMap.adjoint_comp, LinearMap.adjoint_adjoint] using
      trace_symmetric_right ((block Z (some i) none).adjoint.comp (C i)) P hP
  rw [trace_lmi_blocks Z hZ, hI]
  simp only [stateCoefficient, trace_sub_comp, trace_add_comp, trace_sum_comp,
    trace_comp_add, LinearMap.comp_smul, LinearMap.smul_comp, map_smul, smul_eq_mul,
    map_add, map_sum, hC]
  rw [trace_cycle_three (block Z none none) A.adjoint P,
    trace_control_pair (block Z none none) hQ B K]
  simp only [two_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, LinearMap.comp_assoc, Q]
  ring

end LinearStochastic.LMICoefficients

namespace LinearStochastic.LMICoefficients
open scoped BigOperators
open InnerProductSpace ConeBlocks
variable {E U ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [Fintype ι] [DecidableEq ι]

theorem symmetric_trace_separates (Q : E →ₗ[ℝ] E) (hQ : Q.IsSymmetric)
    (hz : ∀ P : E →ₗ[ℝ] E, P.IsSymmetric → LinearMap.trace ℝ E (Q.comp P) = 0) : Q = 0 := by
  apply hQ.inner_map_self_eq_zero.mp
  intro x
  have hp : ((rankOne ℝ x x).toLinearMap).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (PositiveDual.rankOneSelf x).property
  have h := hz _ hp
  change PositiveDual.tracePair Q (rankOne ℝ x x).toLinearMap = 0 at h
  simpa only [PositiveDual.tracePair_rankOne, real_inner_comm] using h

theorem rectangular_trace_separates (I : E →ₗ[ℝ] U)
    (hz : ∀ K : E →ₗ[ℝ] U, LinearMap.trace ℝ E (I.adjoint.comp K) = 0) : I = 0 := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro u
  have h := hz (rankOne ℝ u x).toLinearMap
  have hh : I.adjoint.comp (rankOne ℝ u x).toLinearMap =
      (innerₛₗ ℝ x).smulRight (I.adjoint u) := by
    ext y
    simp
  rw [hh, LinearMap.trace_smulRight] at h
  change inner ℝ x (I.adjoint u) = 0 at h
  simpa only [LinearMap.adjoint_inner_right, LinearMap.zero_apply, inner_zero_left] using h

/-- Annihilation of the actual LMI range forces both coefficient identities;
this is not a premise containing the desired certificate equations. -/
theorem coefficients_of_trace_annihilation
    (Z : BlockSpace E (Option ι) →ₗ[ℝ] BlockSpace E (Option ι)) (hZ : Z.IsSymmetric)
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ)
    (hz : ∀ P : E →ₗ[ℝ] E, P.IsSymmetric → ∀ K : E →ₗ[ℝ] U,
      LinearMap.trace ℝ _ (Z.comp (lmi A B C D ρ P K)) = 0) :
    stateCoefficient Z A C ρ = 0 ∧ inputCoefficient Z B D = 0 := by
  constructor
  · apply symmetric_trace_separates _ (stateCoefficient_symmetric Z hZ A C ρ)
    intro P hP
    have h := hz P hP 0
    rw [trace_lmi_coefficients Z hZ A B C D ρ P hP 0] at h
    simpa using h
  · apply rectangular_trace_separates
    intro K
    have h := hz 0 LinearMap.IsSymmetric.zero K
    rw [trace_lmi_coefficients Z hZ A B C D ρ 0 LinearMap.IsSymmetric.zero K] at h
    simpa using h

/-- Complete cone-alternative proof of arbitrary-rate LMI feasibility in
finite-dimensional real Hilbert coordinates. -/
theorem arbitrary_rate_feasible
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E)
    (hflag : (InputStructure.fromForward A B C D).flag (Module.finrank ℝ E) = ⊥)
    (ρ : ℝ) :
    ∃ (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U), P.IsSymmetric ∧
      PositiveCone.UniformPositive (-(lmi A B C D ρ P K).toContinuousLinearMap) := by
  let L := (-lmiMap A B C D ρ).range
  rcases PositiveDual.strict_positive_or_positive_annihilator L with h | ⟨Z, hZ, hn, hz⟩
  · obtain ⟨T, ⟨p, hp⟩, hT⟩ := h
    refine ⟨p.1.val.toLinearMap, p.2,
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp p.1.property, ?_⟩
    subst T
    exact hT
  · exfalso
    apply hn
    have htrace (P : E →ₗ[ℝ] E) (hP : P.IsSymmetric) (K : E →ₗ[ℝ] U) :
        LinearMap.trace ℝ _ (Z.comp (lmi A B C D ρ P K)) = 0 := by
      have h := hz ((-lmiMap A B C D ρ) (hP.toSelfAdjoint, K))
        ⟨(hP.toSelfAdjoint, K), rfl⟩
      change LinearMap.trace ℝ _ (Z.comp (-lmi A B C D ρ P K)) = 0 at h
      simpa using h
    obtain ⟨hs, hi⟩ := coefficients_of_trace_annihilation Z hZ.isSymmetric A B C D ρ htrace
    apply ConeBlocks.zero_flag_excludes_block_certificate (InputStructure.fromForward A B C D)
      hflag Z hZ ρ
    · simpa only [stateCoefficient, InputStructure.fromForward, LinearMap.adjoint_adjoint,
        sub_eq_zero] using hs
    · exact hi

end LinearStochastic.LMICoefficients

#print axioms LinearStochastic.LMICoefficients.arbitrary_rate_feasible

namespace LinearStochastic.LMICoefficients
open scoped BigOperators
open InnerProductSpace ConeBlocks
variable {E U ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [Fintype ι] [DecidableEq ι]

theorem lmi_noise_diagonal (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U) (i : ι) :
    block (lmi A B C D ρ P K) (some i) (some i) = -P := by
  ext x
  simp [block, lmi, liftBlock, project, inject]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

theorem inject_norm (i : ι) (x : E) : ‖inject i x‖ = ‖x‖ := by
  simp [inject]

/-- Any noise principal block extracts the positive Lyapunov matrix.
The nonempty noise index is the paper's m≥1 hypothesis. -/
theorem positive_lyapunov_of_negative_lmi [Nonempty ι]
    (A : E →ₗ[ℝ] E) (B : U →ₗ[ℝ] E) (C : ι → E →ₗ[ℝ] E)
    (D : ι → U →ₗ[ℝ] E) (ρ : ℝ) (P : E →ₗ[ℝ] E) (K : E →ₗ[ℝ] U)
    (h : PositiveCone.UniformPositive (-(lmi A B C D ρ P K).toContinuousLinearMap)) :
    PositiveCone.UniformPositive P.toContinuousLinearMap := by
  obtain ⟨ε, hε, hb⟩ := h
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine ⟨ε, hε, ?_⟩
  intro x
  have hz := hb (inject (some i) x)
  have hi := block_inner (lmi A B C D ρ P K) (some i) (some i) x x
  rw [lmi_noise_diagonal, LinearMap.neg_apply, inner_neg_left] at hi
  change ε * ‖inject (some i) x‖ ^ 2 ≤
    inner ℝ (-(lmi A B C D ρ P K (inject (some i) x))) (inject (some i) x) at hz
  change ε * ‖x‖ ^ 2 ≤ inner ℝ (P x) x
  simpa only [inner_neg_left, ← hi, neg_neg, inject_norm] using hz

end LinearStochastic.LMICoefficients

#print axioms LinearStochastic.LMICoefficients.positive_lyapunov_of_negative_lmi
