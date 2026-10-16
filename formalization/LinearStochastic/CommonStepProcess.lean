/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
Adapted to a specified common filtration; original pinned MathFin source retained in NOTICE.
-/
import LinearStochastic.CommonItoCLM

noncomputable section
namespace LinearStochastic.CommonItoLocality
open MeasureTheory ProbabilityTheory Filter CommonItoCLM CommonItoL2
open scoped NNReal ENNReal Topology
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}
  [CommonItoIsometry.ForwardIndependent B 𝓕 μ] (hB : IsPreBrownianReal B μ)
/-- The single-step simple process `φ · 𝟙_{(a,b]}` with `φ` bounded by `M` and
`𝓕_a`-measurable. Its terminal Itô integral is `φ·(B_b − B_a)`. -/
noncomputable def stepSP {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {a b : ℝ≥0}
    (hab : a ≤ b) (hbT : b ≤ T) {φ : Ω → ℝ}
    (hφ : Measurable[𝓕 a] φ) {M : ℝ} (hφM : ∀ ω, |φ ω| ≤ M) :
    TBoundedSP (𝓕 := 𝓕) T hBmeas :=
  ⟨{ valueBot := 0
     value := Finsupp.single (a, b) φ
     le_of_mem_support_value := fun p hp ↦ by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       exact hab
     measurable_valueBot := measurable_const
     measurable_value' := fun p hp ↦ by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       rw [Finsupp.single_eq_same]; exact hφ
     bounded_valueBot := ⟨0, by simp⟩
     bounded_value := ⟨M, fun p hp ω ↦ by
       obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
       rw [Finsupp.single_eq_same, Real.norm_eq_abs]; exact hφM ω⟩ },
   fun p hp ↦ by
     obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
     exact hbT⟩

/-- The terminal Itô integral of a single step is `φ·(B_b − B_a)`. -/
lemma itoSimple_stepSP {T : ℝ≥0} (hBmeas : ∀ t, Measurable (B t)) {a b : ℝ≥0}
    (hab : a ≤ b) (hbT : b ≤ T) {φ : Ω → ℝ}
    (hφ : Measurable[𝓕 a] φ) {M : ℝ} (hφM : ∀ ω, |φ ω| ≤ M) (ω : Ω) :
    itoSimple hBmeas (stepSP hBmeas hab hbT hφ hφM).val ω = φ ω * (B b ω - B a ω) := by
  rw [itoSimple_apply]
  show (Finsupp.single (a, b) φ).sum (fun p v ↦ v ω * (B p.2 ω - B p.1 ω))
      = φ ω * (B b ω - B a ω)
  rw [Finsupp.sum_single_index (by simp)]


/-- The elementary Itô integral is additive over a finite sum of simple processes. -/
lemma itoSimple_sum (hBmeas : ∀ t, Measurable (B t)) {ι' : Type*} (s : Finset ι')
    (V : ι' → SimpleProcess ℝ 𝓕) :
    itoSimple hBmeas (∑ i ∈ s, V i) = ∑ i ∈ s, itoSimple hBmeas (V i) := by
  classical
  induction s using Finset.induction with
  | empty => funext ω; simp [itoSimple]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, itoSimple_add, ih]


end LinearStochastic.CommonItoLocality
