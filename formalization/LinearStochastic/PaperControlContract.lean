module

public import LinearStochastic.HilbertS2Energy
public import LinearStochastic.CommonProcessSpace
public import LinearStochastic.PaperControlProperties

@[expose] public section

/-! Exact mathematical conventions for the manuscript's control space,
Euclidean dimensions, intermediate empty matrices, and L² representatives. -/
noncomputable section
namespace LinearStochastic.PaperControlContract
open MeasureTheory ProbabilityTheory Module
open scoped NNReal
open CommonItoMultichannel
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} {r : ℕ}

/-- In the actual Euclidean input space, ordinary progressiveness and strong
progressiveness coincide. Thus no extra admissibility restriction is hidden
in the Hilbert-valued integration interface. -/
theorem progressive_iff_strong (v : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin r)) :
    IsProgressive 𝓕 v ↔ IsStronglyProgressive 𝓕 v :=
  ⟨fun h=>h.isStronglyProgressive,fun h=>h.isProgressive⟩

omit [IsProbabilityMeasure μ] in
/-- Ordinary progressive finite-energy controls have exactly the L²
integrability required by the genuine stochastic integral. -/
theorem energy_iff_memLp [SFinite μ] (T : ℝ≥0) (v : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin r))
    (hv : IsProgressive 𝓕 v) :
    Integrable (fun z : ℝ≥0 × Ω=>‖v z.1 z.2‖^2) ((CommonItoCLM.timeMeasure_T T).prod μ) ↔
      MemLp (Function.uncurry v) 2 ((CommonItoCLM.timeMeasure_T T).prod μ) :=
  (memLp_two_iff_integrable_sq_norm
    (CommonProcessSpace.progressive_spacetime_measurable hv.isStronglyProgressive T)).symm

/-- Every control admitted by the paper has a genuine predictable L² class
with exactly its original values almost everywhere and exactly its real-clock
expected energy. This is a proved representative theorem, not an assumption. -/
theorem ordinary_control_class (T : ℝ≥0) (v : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin r))
    (hv : IsProgressive 𝓕 v)
    (he : Integrable (fun z : ℝ≥0 × Ω=>‖v z.1 z.2‖^2) ((CommonItoCLM.timeMeasure_T T).prod μ)) :
    ∃ u : Lp (EuclideanSpace ℝ (Fin r)) 2 (spacetimeMeasure 𝓕 μ T),
      (u : ℝ≥0 × Ω → EuclideanSpace ℝ (Fin r)) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry v ∧
      ‖u‖^2=∫ ω,(∫ t in Set.Ioc 0 (T:ℝ),‖v t.toNNReal ω‖^2) ∂μ := by
  have hv2 := (energy_iff_memLp T v hv).mp he
  obtain ⟨u,hu⟩ := ProgressivePredictable.exists_predictable_Lp μ hv.isStronglyProgressive T 2 hv2
  exact ⟨u,hu,HilbertS2Energy.control_energy T v u hv2 hu⟩

omit [IsProbabilityMeasure μ] in
/-- The predictable L² class does not depend on a choice of representative. -/
theorem control_class_unique (T : ℝ≥0) (v : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin r))
    (u u' : Lp (EuclideanSpace ℝ (Fin r)) 2 (spacetimeMeasure 𝓕 μ T))
    (hu : (u : ℝ≥0 × Ω → EuclideanSpace ℝ (Fin r)) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry v)
    (hu' : (u' : ℝ≥0 × Ω → EuclideanSpace ℝ (Fin r)) =ᵐ[(CommonItoCLM.timeMeasure_T T).prod μ] Function.uncurry v) : u=u' := by
  apply Lp.ext
  exact (Lp.stronglyMeasurable u).ae_eq_trim_of_stronglyMeasurable 𝓕.predictable_le_prod
    (Lp.stronglyMeasurable u') (hu.trans hu'.symm)

/-- The state, input and joint-noise Hilbert spaces have exactly the paper's
n, r and mn dimensions. The identity also covers empty intermediate types. -/
theorem euclidean_dimensions (n r m : ℕ) :
    finrank ℝ (EuclideanSpace ℝ (Fin n))=n ∧
    finrank ℝ (EuclideanSpace ℝ (Fin r))=r ∧
    finrank ℝ (PiLp 2 (fun _ : Fin m=>EuclideanSpace ℝ (Fin n)))=m*n := by
  refine ⟨finrank_euclideanSpace_fin,finrank_euclideanSpace_fin,?_⟩
  rw [(WithLp.linearEquiv 2 ℝ (Fin m→EuclideanSpace ℝ (Fin n))).finrank_eq]
  simp [Module.finrank_pi_fintype]

/-- The literal stacked diffusion matrix has mn rows and r columns. -/
theorem stacked_dimensions (n r m : ℕ) :
    Fintype.card (Fin m×Fin n)=m*n ∧ Fintype.card (Fin r)=r := by simp

/-- Empty-row and empty-column intermediate matrices obey the ordinary
zero-rank convention, without redefining rank for degenerate stages. -/
theorem empty_rank (a b : ℕ) (M : Matrix (Fin 0) (Fin b) ℝ) (N : Matrix (Fin a) (Fin 0) ℝ) :
    M.rank=0 ∧ N.rank=0 := by
  have hM : M=0 := Subsingleton.elim _ _
  have hN : N=0 := Subsingleton.elim _ _
  simp [hM,hN]

end LinearStochastic.PaperControlContract
