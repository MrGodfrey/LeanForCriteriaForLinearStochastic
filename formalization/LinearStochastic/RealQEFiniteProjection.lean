module

public import LinearStochastic.RealQEExistential
public import LinearStochastic.SemialgebraicLogic
public import Mathlib.Data.Fintype.Option

@[expose] public section

noncomputable section
namespace LinearStochastic.RealQEFiniteProjection
open SemialgebraicCoordinates RealQEExistential
universe u v
variable {σ : Type u}

/-- Projection along any finite block of real coordinates, obtained by repeated
single-real elimination and explicit coordinate renaming. -/
theorem exists_finite {ι : Type v} [Finite ι] (S : Set (σ ⊕ ι → ℝ))
    (hS : IsSemialgebraic S) : IsSemialgebraic {v | ∃ u : ι → ℝ, Sum.elim v u ∈ S} := by
  have hall : ∀ (ι : Type v) [Finite ι], ∀ S : Set (σ ⊕ ι → ℝ),
      IsSemialgebraic S → IsSemialgebraic {v | ∃ u : ι → ℝ, Sum.elim v u ∈ S} := by
    intro ι _
    apply Finite.induction_empty_option
      (P := fun ι => ∀ S : Set (σ ⊕ ι → ℝ), IsSemialgebraic S →
        IsSemialgebraic {v | ∃ u : ι → ℝ, Sum.elim v u ∈ S})
    · intro α β e ih S hS
      let f : σ ⊕ β → σ ⊕ α := Sum.map id e.symm
      have h := ih {w | w ∘ f ∈ S} (hS.rename_preimage f)
      convert h using 1
      ext v
      constructor
      · rintro ⟨u,hu⟩
        refine ⟨u ∘ e,?_⟩
        have he : Sum.elim v (u ∘ e) ∘ f = Sum.elim v u := by
          funext i
          cases i <;> simp [f,Function.comp_def]
        change Sum.elim v (u ∘ e) ∘ f ∈ S
        rwa [he]
      · rintro ⟨u,hu⟩
        refine ⟨u ∘ e.symm,?_⟩
        have he : Sum.elim v u ∘ f = Sum.elim v (u ∘ e.symm) := by
          funext i
          cases i <;> rfl
        change Sum.elim v u ∘ f ∈ S at hu
        rwa [he] at hu
    · intro S hS
      let f : σ ⊕ PEmpty → σ := Sum.elim id PEmpty.elim
      have h := hS.rename_preimage f
      convert h using 1
      ext v
      constructor
      · rintro ⟨u,hu⟩
        have he : Sum.elim v u = v ∘ f := by
          funext i
          cases i with
          | inl a => rfl
          | inr a => exact a.elim
        change v ∘ f ∈ S
        rwa [←he]
      · intro hv
        refine ⟨PEmpty.elim,?_⟩
        have he : Sum.elim v PEmpty.elim = v ∘ f := by
          funext i
          cases i with
          | inl a => rfl
          | inr a => exact a.elim
        rwa [he]
    · intro α _ ih S hS
      let f : σ ⊕ Option α → Option (σ ⊕ α) := fun i => match i with
        | .inl s => some (.inl s)
        | .inr none => none
        | .inr (some a) => some (.inr a)
      have h := ih {w | ∃ x : ℝ, extend w x ∘ f ∈ S}
        (exists_option {z | z ∘ f ∈ S} (hS.rename_preimage f))
      convert h using 1
      ext v
      constructor
      · rintro ⟨u,hu⟩
        refine ⟨fun a => u (some a),u none,?_⟩
        have he : extend (Sum.elim v (fun a => u (some a))) (u none) ∘ f = Sum.elim v u := by
          funext i
          rcases i with s | (_|a) <;> rfl
        change extend (Sum.elim v (fun a => u (some a))) (u none) ∘ f ∈ S
        rwa [he]
      · rintro ⟨u,x,hux⟩
        refine ⟨fun a => Option.elim a x u,?_⟩
        have he : extend (Sum.elim v u) x ∘ f = Sum.elim v (fun a => Option.elim a x u) := by
          funext i
          rcases i with s | (_|a) <;> rfl
        change extend (Sum.elim v u) x ∘ f ∈ S at hux
        rwa [he] at hux
  exact hall ι S hS

/-- Universal finite real blocks follow by complement and existential elimination. -/
theorem forall_finite {ι : Type v} [Finite ι] (S : Set (σ ⊕ ι → ℝ))
    (hS : IsSemialgebraic S) : IsSemialgebraic {v | ∀ u : ι → ℝ, Sum.elim v u ∈ S} := by
  simpa only [Set.compl_ofPred,Set.mem_compl_iff,not_exists,not_not] using
    (exists_finite Sᶜ hS.compl).compl

end LinearStochastic.RealQEFiniteProjection
