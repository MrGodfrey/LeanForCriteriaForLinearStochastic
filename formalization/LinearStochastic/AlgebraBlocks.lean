import LinearStochastic.AlgebraRank

/-!
# Recursive block pair of paper (eq:pair)

The product spaces are the three displayed row and column blocks. Thus this
representation retains the actual linear maps of the paper without choosing
irrelevant coordinate-flattening permutations. Index `k` represents paper `k+1`.
-/
noncomputable section

namespace LinearStochastic
open Module
open scoped BigOperators

/-- A finite-dimensional pair of linear maps with a common row space. -/
structure BlockPair (E : Type) [AddCommGroup E] [Module ℝ E] where
  Aux : Type
  Rows : Type
  [auxGroup : AddCommGroup Aux]
  [auxModule : Module ℝ Aux]
  [rowsGroup : AddCommGroup Rows]
  [rowsModule : Module ℝ Rows]
  [auxFinite : FiniteDimensional ℝ Aux]
  [rowsFinite : FiniteDimensional ℝ Rows]
  K : E →ₗ[ℝ] Rows
  N : Aux →ₗ[ℝ] Rows

attribute [instance] BlockPair.auxGroup BlockPair.auxModule BlockPair.rowsGroup
  BlockPair.rowsModule BlockPair.auxFinite BlockPair.rowsFinite

namespace AdjointCoefficients
variable {E U ι : Type} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup U] [Module ℝ U] [Fintype ι]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ U]
variable (s : AdjointCoefficients (𝕜 := ℝ) (E := E) (U := U) (ι := ι))

private def sumC : (ι → E) →ₗ[ℝ] E := ∑ i, (s.C i).comp (LinearMap.proj i)
private def sumD : (ι → E) →ₗ[ℝ] U := ∑ i, (s.D i).comp (LinearMap.proj i)

/-- Initial pair `(Bᵀ, Dᵀ)` from (eq:pair-start). -/
def firstPair : BlockPair E where
  Aux := ι → E
  Rows := U
  K := s.B
  N := s.sumD

/-- Literal three-by-three block recursion from (eq:pair). -/
def nextPair (p : BlockPair E) : BlockPair E where
  Aux := (ι → E) × ((ι → p.Aux) × p.Aux)
  Rows := U × ((ι → p.Rows) × p.Rows)
  K := s.B.prod ((0 : E →ₗ[ℝ] (ι → p.Rows)).prod (p.K.comp s.A))
  N :=
    let w := LinearMap.fst ℝ (ι → E) ((ι → p.Aux) × p.Aux)
    let a := (LinearMap.fst ℝ (ι → p.Aux) p.Aux).comp
      (LinearMap.snd ℝ (ι → E) ((ι → p.Aux) × p.Aux))
    let b := (LinearMap.snd ℝ (ι → p.Aux) p.Aux).comp
      (LinearMap.snd ℝ (ι → E) ((ι → p.Aux) × p.Aux))
    (s.sumD.comp w).prod
      ((LinearMap.pi (fun i => (p.K.comp ((LinearMap.proj i).comp w)) +
        p.N.comp ((LinearMap.proj i).comp a))).prod
      ((p.K.comp (s.sumC.comp w)) + p.N.comp b))

/-- No stopping or rank assumptions are built into this recursive construction. -/
def blockPair (k : ℕ) : BlockPair E := Nat.rec s.firstPair (fun _ p => s.nextPair p) k

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ U] in
/-- The otherwise implicit `v ∈ Vₖ` condition follows from the recursive witnesses. -/
theorem flag_mem_of_constraints (k : ℕ) (v : E) (w : ι → E)
    (hw : ∀ i, w i ∈ s.flag k)
    (hB : s.B v + ∑ i, s.D i (w i) = 0)
    (hA : s.A v + ∑ i, s.C i (w i) ∈ s.flag k) : v ∈ s.flag (k + 1) := by
  induction k with
  | zero => exact ⟨Submodule.mem_top, w, hw, hB, hA⟩
  | succ k ih =>
    have hv : v ∈ s.flag (k + 1) :=
      ih (fun i => s.flag_step_le k (hw i)) (s.flag_step_le k hA)
    exact ⟨hv, w, hw, hB, hA⟩

/-- The main existential block representation, paper (eq:rank-identity). -/
theorem blockPair_represents_flag (k : ℕ) :
    feasibleSpace (s.blockPair k).K (s.blockPair k).N = s.flag (k + 1) := by
  induction k with
  | zero =>
    ext v
    rw [mem_feasibleSpace]
    change (∃ w : ι → E, s.B v + s.sumD w = 0) ↔ v ∈ s.obstruction (⊤ : Submodule ℝ E)
    simp [mem_obstruction, sumD, LinearMap.sum_apply]
  | succ k ih =>
    ext v
    rw [mem_feasibleSpace]
    change (∃ a : (ι → E) × ((ι → (s.blockPair k).Aux) × (s.blockPair k).Aux),
      (s.nextPair (s.blockPair k)).K v + (s.nextPair (s.blockPair k)).N a = 0) ↔ _
    constructor
    · rintro ⟨⟨w, α, β⟩, h⟩
      have hB := congrArg Prod.fst h
      have hW := congrArg (fun x => x.2.1) h
      have hA := congrArg (fun x => x.2.2) h
      change s.B v + s.sumD w = 0 at hB
      change (0 : ι → (s.blockPair k).Rows) +
        (fun i => (s.blockPair k).K (w i) + (s.blockPair k).N (α i)) = 0 at hW
      rw [zero_add] at hW
      change (s.blockPair k).K (s.A v) +
        ((s.blockPair k).K (s.sumC w) + (s.blockPair k).N β) = 0 at hA
      simp only [sumD, sumC, LinearMap.sum_apply, LinearMap.comp_apply,
        LinearMap.proj_apply] at hB hA
      apply s.flag_mem_of_constraints (k + 1) v w
      · intro i
        rw [← ih, mem_feasibleSpace]
        exact ⟨α i, congrFun hW i⟩
      · exact hB
      · rw [← ih, mem_feasibleSpace]
        exact ⟨β, by simpa only [map_add, add_assoc] using hA⟩
    · intro hv
      obtain ⟨_, w, hw, hB, hA⟩ := hv
      have hα : ∀ i, ∃ a, (s.blockPair k).K (w i) + (s.blockPair k).N a = 0 := by
        intro i
        exact (mem_feasibleSpace _ _ _).mp (ih.symm ▸ hw i)
      choose α hα using hα
      change s.A v + ∑ i, s.C i (w i) ∈ s.flag (k + 1) at hA
      obtain ⟨β, hβ⟩ := (mem_feasibleSpace _ _ _).mp (ih.symm ▸ hA)
      refine ⟨(w, α, β), ?_⟩
      apply Prod.ext
      · change s.B v + s.sumD w = 0
        simpa [sumD, LinearMap.sum_apply] using hB
      · apply Prod.ext
        · change (0 : ι → (s.blockPair k).Rows) +
            (fun i => (s.blockPair k).K (w i) + (s.blockPair k).N (α i)) = 0
          rw [zero_add]
          exact funext hα
        · change (s.blockPair k).K (s.A v) +
            ((s.blockPair k).K (s.sumC w) + (s.blockPair k).N β) = 0
          simpa [sumC, LinearMap.sum_apply, map_add, add_assoc] using hβ

/-- Paper (eq:rank-codimension) for the actual recursively constructed block maps. -/
theorem blockPair_rank_codimension (k : ℕ) :
    finrank ℝ ((s.blockPair k).N.coprod (s.blockPair k).K).range -
      finrank ℝ (s.blockPair k).N.range =
        finrank ℝ E - finrank ℝ (s.flag (k + 1)) := by
  rw [← s.blockPair_represents_flag]
  exact rank_difference_eq_codimension _ _

/-- Exact row-size recurrence aₖ₊₁ = r + (m+1)aₖ. -/
theorem nextPair_rows_finrank (p : BlockPair E) :
    finrank ℝ (s.nextPair p).Rows =
      finrank ℝ U + (Fintype.card ι + 1) * finrank ℝ p.Rows := by
  change finrank ℝ (U × ((ι → p.Rows) × p.Rows)) = _
  simp [Module.finrank_prod, Module.finrank_pi_fintype]
  ring

/-- Exact column-size recurrence bₖ₊₁ = mn + (m+1)bₖ. -/
theorem nextPair_aux_finrank (p : BlockPair E) :
    finrank ℝ (s.nextPair p).Aux =
      Fintype.card ι * finrank ℝ E + (Fintype.card ι + 1) * finrank ℝ p.Aux := by
  change finrank ℝ ((ι → E) × ((ι → p.Aux) × p.Aux)) = _
  simp [Module.finrank_prod, Module.finrank_pi_fintype]
  ring

/-- The exact geometric-sum row dimension stated before paper (eq:pair). -/
theorem blockPair_rows_finrank (k : ℕ) :
    finrank ℝ (s.blockPair k).Rows =
      finrank ℝ U * ∑ l ∈ Finset.range (k + 1), (Fintype.card ι + 1) ^ l := by
  induction k with
  | zero =>
    change finrank ℝ U = _
    simp
  | succ k ih =>
    change finrank ℝ (s.nextPair (s.blockPair k)).Rows = _
    rw [s.nextPair_rows_finrank, ih, geom_sum_succ (n := k + 1)]
    ring

/-- The exact geometric-sum column dimension stated before paper (eq:pair). -/
theorem blockPair_aux_finrank (k : ℕ) :
    finrank ℝ (s.blockPair k).Aux =
      (Fintype.card ι * finrank ℝ E) *
        ∑ l ∈ Finset.range (k + 1), (Fintype.card ι + 1) ^ l := by
  induction k with
  | zero =>
    change finrank ℝ (ι → E) = _
    simp [Module.finrank_pi_fintype]
  | succ k ih =>
    change finrank ℝ (s.nextPair (s.blockPair k)).Aux = _
    rw [s.nextPair_aux_finrank, ih, geom_sum_succ (n := k + 1)]
    ring

/-- Real coefficient specialization of the paper's rank-codimension formula.
The code index k represents the paper index k+1. -/
theorem matrix_blockPair_rank_codimension {n r m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin r) ℝ)
    (C : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (D : Fin m → Matrix (Fin n) (Fin r) ℝ) (k : ℕ) :
    let s := fromMatrices A B C D
    finrank ℝ ((s.blockPair k).N.coprod (s.blockPair k).K).range -
      finrank ℝ (s.blockPair k).N.range = n - finrank ℝ (s.flag (k + 1)) := by
  simpa using (fromMatrices A B C D).blockPair_rank_codimension k

#print axioms blockPair_represents_flag
#print axioms blockPair_rank_codimension
end AdjointCoefficients
end LinearStochastic
