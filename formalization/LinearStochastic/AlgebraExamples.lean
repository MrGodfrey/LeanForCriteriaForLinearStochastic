import LinearStochastic.AlgebraFlagTransport

/-!
# The manuscript's concrete coefficient families

All coefficients are actual real matrices. `SingularDiffusion` is
ex:singular-diffusion. `Nonrobustness` uses m+1 noise channels, representing
every strictly positive noise count in rem:nonrobustness. Only the algebraic
flag and matrix-rank claims are proved here; no stochastic classification is
assumed, and no assertion about random terminal targets is added.
-/
noncomputable section
namespace LinearStochastic.Examples
open Module
open scoped BigOperators Matrix

namespace SingularDiffusion

def B : Matrix (Fin 1) (Fin 3) ℝ := !![1, 0, 0]
def D (ε : ℝ) : Fin 2 → Matrix (Fin 1) (Fin 3) ℝ :=
  ![!![0, 1, 0], !![0, 1, ε]]
def coefficients (ε : ℝ) := AdjointCoefficients.fromMatrices (0 : Matrix (Fin 1) (Fin 1) ℝ)
  B (fun _ : Fin 2 => 0) (D ε)

/-- The exact displayed observation vector of ex:singular-diffusion. -/
theorem observation (ε : ℝ) (v : Fin 1 → ℝ) (w : Fin 2 → Fin 1 → ℝ) :
    (coefficients ε).B v + ∑ j, (coefficients ε).D j (w j) =
      ![v 0, w 0 0 + w 1 0, ε * w 1 0] := by
  ext i
  fin_cases i <;> simp [coefficients, AdjointCoefficients.fromMatrices, B, D,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The first obstruction is zero for every parameter, including ε=0. -/
theorem flag_one (ε : ℝ) : (coefficients ε).flag 1 = ⊥ := by
  apply bot_unique
  intro v hv
  obtain ⟨_, w, _, hB, _⟩ := hv
  rw [observation] at hB
  change v = 0
  ext i
  fin_cases i
  exact congrFun hB 0

/-- Every individual diffusion row is surjective, even when the joint diffusion is singular. -/
theorem each_diffusion_range (ε : ℝ) (i : Fin 2) : (D ε i).mulVecLin.range = ⊤ := by
  apply LinearMap.range_eq_top.mpr
  intro y
  refine ⟨![0, y 0, 0], ?_⟩
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [D,  Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem each_diffusion_rank (ε : ℝ) (i : Fin 2) : (D ε i).rank = 1 := by
  rw [Matrix.rank, each_diffusion_range, finrank_top]
  simp

/-- Their horizontal concatenation has full row rank for every ε too. -/
theorem horizontal_diffusion_rank (ε : ℝ) : (Coordinates.joint (D ε)).rank = 1 := by
  have hr : (Coordinates.joint (D ε)).mulVecLin.range = ⊤ := by
    rw [WordMatrices.range_joint]
    apply top_unique
    rw [← each_diffusion_range ε 0]
    exact le_iSup (fun i => (D ε i).mulVecLin.range) 0
  rw [Matrix.rank, hr, finrank_top]
  simp

/-- At ε=0, the actual vertical stack has one-dimensional image. -/
theorem joint_rank_zero : (SurjectiveMatrices.stack (D 0)).rank = 1 := by
  let c : ℝ →ₗ[ℝ] ((Fin 2 × Fin 1) → ℝ) := LinearMap.pi (fun _ => LinearMap.id)
  have hc : Function.Injective c := by
    intro a b h
    exact congrFun h (0,0)
  have hr : (SurjectiveMatrices.stack (D 0)).mulVecLin.range = c.range := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      refine ⟨u 1, ?_⟩
      ext p
      rcases p with ⟨i,j⟩
      fin_cases i <;> fin_cases j <;>
        simp [c, SurjectiveMatrices.stack, D, 
          Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · rintro ⟨a, rfl⟩
      refine ⟨![0,a,0], ?_⟩
      ext p
      rcases p with ⟨i,j⟩
      fin_cases i <;> fin_cases j <;>
        simp [c, SurjectiveMatrices.stack, D, 
          Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  rw [Matrix.rank, hr, LinearMap.finrank_range_of_inj hc, Module.finrank_self]

/-- At ε≠0, the actual vertical stack has full rank two. -/
theorem joint_rank_ne_zero (ε : ℝ) (hε : ε ≠ 0) :
    (SurjectiveMatrices.stack (D ε)).rank = 2 := by
  have hr : (SurjectiveMatrices.stack (D ε)).mulVecLin.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    intro y
    refine ⟨![0,y (0,0),(y (1,0)-y (0,0))/ε], ?_⟩
    ext p
    rcases p with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [SurjectiveMatrices.stack, D, 
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    field_simp
    ring
  rw [Matrix.rank, hr, finrank_top]
  simp

/-- The complete joint-rank dichotomy, for the literal stacked matrix. -/
theorem joint_rank (ε : ℝ) :
    (SurjectiveMatrices.stack (D ε)).rank = if ε = 0 then 1 else 2 := by
  by_cases hε : ε = 0
  · subst ε
    simpa using joint_rank_zero
  · simpa [hε] using joint_rank_ne_zero ε hε

#print axioms flag_one
#print axioms joint_rank_zero
#print axioms joint_rank_ne_zero
end SingularDiffusion


namespace Nonrobustness

def A : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
def B : Matrix (Fin 2) (Fin 1) ℝ := !![0; 1]
def C (m : ℕ) (ε : ℝ) (j : Fin (m+1)) : Matrix (Fin 2) (Fin 2) ℝ :=
  if j = 0 then ε • A else 0
def coefficients (m : ℕ) (ε : ℝ) := AdjointCoefficients.fromMatrices A B (C m ε)
  (fun _ : Fin (m+1) => (0 : Matrix (Fin 2) (Fin 1) ℝ))
def firstAxis : Submodule ℝ (Fin 2 → ℝ) := ℝ ∙ ![1,0]

theorem mem_firstAxis (v : Fin 2 → ℝ) : v ∈ firstAxis ↔ v 1 = 0 := by
  constructor
  · intro h
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp h
    simp
  · intro h
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v 0, ?_⟩
    ext i
    fin_cases i <;> simp [h]

/-- The observation constraint is v₂=0 for every number of noise channels. -/
theorem observation (m : ℕ) (ε : ℝ) (v : Fin 2 → ℝ)
    (w : Fin (m+1) → Fin 2 → ℝ) :
    (coefficients m ε).B v + ∑ j, (coefficients m ε).D j (w j) = ![v 1] := by
  ext i
  fin_cases i
  simp [coefficients, AdjointCoefficients.fromMatrices, B, Matrix.toLin'_apply,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- The exact remaining drift constraint displayed in rem:nonrobustness. -/
theorem drift (m : ℕ) (ε : ℝ) (v : Fin 2 → ℝ)
    (w : Fin (m+1) → Fin 2 → ℝ) :
    (coefficients m ε).A v + ∑ j, (coefficients m ε).C j (w j) =
      ![0, v 0 + ε * w 0 0] := by
  have hc (j : Fin (m+1)) : (coefficients m ε).C j (w j) =
      if j = 0 then ![0, ε * w 0 0] else 0 := by
    by_cases hj : j = 0
    · subst j
      ext i
      fin_cases i <;> simp [coefficients, AdjointCoefficients.fromMatrices, C, A,
        Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · simp [coefficients, AdjointCoefficients.fromMatrices, C, hj]
  simp only [hc, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ext i
  fin_cases i <;> simp [coefficients, AdjointCoefficients.fromMatrices, A,
    Matrix.toLin'_apply]

theorem flag_one (m : ℕ) (ε : ℝ) : (coefficients m ε).flag 1 = firstAxis := by
  ext v
  constructor
  · rintro ⟨_, w, _, hb, _⟩
    rw [observation] at hb
    exact (mem_firstAxis v).mpr (congrFun hb 0)
  · intro hv
    refine ⟨Submodule.mem_top, fun _ => 0, fun _ => Submodule.mem_top, ?_, Submodule.mem_top⟩
    rw [observation]
    ext i
    fin_cases i
    exact (mem_firstAxis v).mp hv

/-- With zero perturbation the second obstruction vanishes. -/
theorem flag_two_zero (m : ℕ) : (coefficients m 0).flag 2 = ⊥ := by
  apply bot_unique
  intro v hv
  change v = 0
  change v ∈ (coefficients m 0).obstruction ((coefficients m 0).flag 1) at hv
  rw [flag_one] at hv
  obtain ⟨hv, w, _, _, ha⟩ := hv
  rw [mem_firstAxis] at hv
  rw [drift, mem_firstAxis] at ha
  simp at ha
  ext i
  fin_cases i
  · exact ha
  · exact hv

/-- With any nonzero perturbation the second obstruction remains the entire first axis. -/
theorem flag_two_ne_zero (m : ℕ) (ε : ℝ) (hε : ε ≠ 0) :
    (coefficients m ε).flag 2 = firstAxis := by
  change (coefficients m ε).obstruction ((coefficients m ε).flag 1) = firstAxis
  rw [flag_one]
  apply le_antisymm ((coefficients m ε).obstruction_le firstAxis)
  intro v hv
  refine ⟨hv,
    fun j => if j = 0 then ![-v 0 / ε, 0] else 0, ?_, ?_, ?_⟩
  · intro j
    rw [mem_firstAxis]
    by_cases hj : j = 0 <;> simp [hj]
  · rw [observation]
    ext i
    fin_cases i
    exact (mem_firstAxis v).mp hv
  · rw [drift, mem_firstAxis]
    simp
    field_simp
    ring

/-- The nontrivial stable axis is one dimensional. -/
theorem firstAxis_finrank : finrank ℝ firstAxis = 1 := by
  apply finrank_span_singleton
  intro h
  have hh := congrFun h 0
  norm_num at hh

/-- The exact prescribed rank difference is two at ε=0. -/
theorem delta_two_zero (m : ℕ) :
    let p := (coefficients m 0).blockPair 1
    finrank ℝ (p.N.coprod p.K).range - finrank ℝ p.N.range = 2 := by
  dsimp only
  rw [AdjointCoefficients.blockPair_rank_codimension, flag_two_zero]
  simp

/-- It drops to one for every nonzero ε. -/
theorem delta_two_ne_zero (m : ℕ) (ε : ℝ) (hε : ε ≠ 0) :
    let p := (coefficients m ε).blockPair 1
    finrank ℝ (p.N.coprod p.K).range - finrank ℝ p.N.range = 1 := by
  dsimp only
  rw [AdjointCoefficients.blockPair_rank_codimension, flag_two_ne_zero m ε hε, firstAxis_finrank]
  simp

/-- The prescribed finite rectangular matrices themselves have rank difference two at zero. -/
theorem finitePair_delta_two_zero (m : ℕ) :
    let p := Coordinates.finitePair A B (C m 0)
      (fun _ : Fin (m+1) => (0 : Matrix (Fin 2) (Fin 1) ℝ)) 1
    (Matrix.fromCols p.2 p.1).rank - p.2.rank = 2 := by
  dsimp only
  rw [Coordinates.finitePair_rank_codimension]
  change 2 - finrank ℝ ((coefficients m 0).flag 2) = 2
  rw [flag_two_zero]
  simp

/-- Their rank difference is one at every nonzero perturbation. -/
theorem finitePair_delta_two_ne_zero (m : ℕ) (ε : ℝ) (hε : ε ≠ 0) :
    let p := Coordinates.finitePair A B (C m ε)
      (fun _ : Fin (m+1) => (0 : Matrix (Fin 2) (Fin 1) ℝ)) 1
    (Matrix.fromCols p.2 p.1).rank - p.2.rank = 1 := by
  dsimp only
  rw [Coordinates.finitePair_rank_codimension]
  change 2 - finrank ℝ ((coefficients m ε).flag 2) = 1
  rw [flag_two_ne_zero m ε hε, firstAxis_finrank]

/-- The joint diffusion-control matrix vanishes throughout this family. -/
theorem joint_diffusion_rank (m : ℕ) :
    (SurjectiveMatrices.stack
      (fun _ : Fin (m+1) => (0 : Matrix (Fin 2) (Fin 1) ℝ))).rank = 0 := by
  change (0 : Matrix (Fin (m+1) × Fin 2) (Fin 1) ℝ).rank = 0
  exact Matrix.rank_zero

#print axioms flag_two_zero
#print axioms flag_two_ne_zero
#print axioms delta_two_ne_zero
end Nonrobustness
end LinearStochastic.Examples
