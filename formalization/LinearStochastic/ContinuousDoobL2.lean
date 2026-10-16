import MathFin.Foundations.DoobLpMaximalInequality
import BrownianMotion.Auxiliary.Martingale
import Mathlib.Data.Finset.Sort
import Mathlib

/-!
# Strong L² Doob inequality for continuous martingales

The discrete maximal inequality is imported from the unchanged MathFin commit
99b836298731c432a6242fdb6cb51c1c97f37902. This file proves the continuous-time
extension by ordered finite sampling, density, and Fatou. It does not use the
unproved continuous-time strong Doob declarations in BrownianMotion.DoobLp.
-/

noncomputable section
namespace LinearStochastic.ContinuousDoobL2
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

/-- Ordered enumeration of a finite time set, held at its last time thereafter. -/
def grid (s : Finset ℝ≥0) (hs : s.Nonempty) (k : ℕ) : ℝ≥0 :=
  s.orderEmbOfFin rfl ⟨min k (s.card-1),
    lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (Finset.card_pos.mpr hs) (by omega))⟩

theorem grid_monotone (s : Finset ℝ≥0) (hs : s.Nonempty) : Monotone (grid s hs) := by
  intro i j hij
  apply (s.orderEmbOfFin rfl).monotone
  exact min_le_min_right _ hij

theorem grid_mem (s : Finset ℝ≥0) (hs : s.Nonempty) (k : ℕ) : grid s hs k ∈ s :=
  s.orderEmbOfFin_mem rfl _

theorem grid_last (s : Finset ℝ≥0) (hs : s.Nonempty) : grid s hs (s.card-1) = s.max' hs := by
  simpa only [grid, min_self] using s.orderEmbOfFin_last rfl (Finset.card_pos.mpr hs)

theorem exists_grid (s : Finset ℝ≥0) (hs : s.Nonempty) {t : ℝ≥0} (ht : t ∈ s) :
    ∃ k < (s.card-1)+1, grid s hs k = t := by
  let i : Fin s.card := (s.orderIsoOfFin rfl).symm ⟨t,ht⟩
  have hicard := i.isLt
  have hcard := Finset.card_pos.mpr hs
  refine ⟨i.val, by omega, ?_⟩
  have he : (⟨min i.val (s.card-1),
      lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hcard (by omega))⟩ : Fin s.card) = i := by
    apply Fin.ext
    exact min_eq_left (by omega)
  unfold grid
  rw [he]
  exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨t,ht⟩)

theorem finite_max_eq_grid (s : Finset ℝ≥0) (hs : s.Nonempty) (f : ℝ≥0 → ℝ) :
    s.sup' hs f = (Finset.range ((s.card-1)+1)).sup' Finset.nonempty_range_add_one
      (fun k ↦ f (grid s hs k)) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro t ht
    obtain ⟨k,hk,he⟩ := exists_grid s hs ht
    rw [← he]
    exact Finset.le_sup' (f := fun j ↦ f (grid s hs j)) (Finset.mem_range.mpr hk)
  · apply Finset.sup'_le
    intro k hk
    exact Finset.le_sup' (f := f) (grid_mem s hs k)

/-- Strong L² Doob bound on every actual finite time set, obtained by ordered
sampling from the fully proved discrete theorem. -/
theorem finite_max_eLpNorm_le {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}
    (hX : Martingale X 𝓕 μ) (s : Finset ℝ≥0) (hs : s.Nonempty) :
    eLpNorm (fun ω ↦ s.sup' hs (fun t ↦ ‖X t ω‖)) 2 μ ≤
      2 * eLpNorm (X (s.max' hs)) 2 μ := by
  have hsample := hX.indexComap (grid_monotone s hs)
  have h := hsample.eLpNorm_norm_runMax_le (p:=2) (by norm_num) (s.card-1)
  have he : (fun ω ↦ s.sup' hs (fun t ↦ ‖X t ω‖)) =
      (fun ω ↦ (Finset.range ((s.card-1)+1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ ‖X (grid s hs k) ω‖)) := funext fun ω ↦ finite_max_eq_grid s hs _
  rw [he]
  simpa only [show ENNReal.ofReal (2 : ℝ)=2 by norm_num,
    show ENNReal.ofReal ((2 : ℝ)/(2-1))=2 by norm_num, Function.comp_apply, grid_last] using h



/-- An arbitrary dense sampling, always including the terminal time. -/
def sampleSet (T : ℝ≥0) (q : ℕ → Set.Iic T) (n : ℕ) : Finset ℝ≥0 :=
  insert T ((Finset.range n).image (fun k ↦ (q k).val))

theorem sampleSet_nonempty (T : ℝ≥0) (q : ℕ → Set.Iic T) (n : ℕ) :
    (sampleSet T q n).Nonempty := ⟨T, Finset.mem_insert_self _ _⟩

theorem sampleSet_le (T : ℝ≥0) (q : ℕ → Set.Iic T) (n : ℕ)
    {t : ℝ≥0} (ht : t ∈ sampleSet T q n) : t ≤ T := by
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact le_rfl
  · rcases Finset.mem_image.mp ht with ⟨k,hk,rfl⟩
    exact (q k).property

theorem sampleSet_max (T : ℝ≥0) (q : ℕ → Set.Iic T) (n : ℕ) :
    (sampleSet T q n).max' (sampleSet_nonempty T q n) = T := by
  apply le_antisymm
  · exact sampleSet_le T q n (Finset.max'_mem _ _)
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)

theorem sampleSet_monotone (T : ℝ≥0) (q : ℕ → Set.Iic T) :
    Monotone (sampleSet T q) := by
  intro i j hij
  apply Finset.insert_subset_insert
  exact Finset.image_subset_image (Finset.range_mono hij)

/-- The actual pathwise supremum over the whole closed time interval. -/
def pathSup {Ω E : Type*} [NormedAddCommGroup E]
    (X : ℝ≥0 → Ω → E) (T : ℝ≥0) (ω : Ω) : ℝ :=
  ⨆ t : Set.Iic T, ‖X t.val ω‖

theorem norm_range_bddAbove {Ω E : Type*} [NormedAddCommGroup E]
    (X : ℝ≥0 → Ω → E) (T : ℝ≥0) (ω : Ω)
    (hc : Continuous (fun t ↦ X t ω)) :
    BddAbove (Set.range (fun t : Set.Iic T ↦ ‖X t.val ω‖)) := by
  have hcomp : IsCompact (Set.Iic T) := by
    rw [← Set.Icc_bot]
    exact isCompact_Icc
  have h := hcomp.bddAbove_image hc.norm.continuousOn
  simpa only [Set.image_eq_range] using h

theorem sampled_max_tendsto {Ω E : Type*} [NormedAddCommGroup E]
    (X : ℝ≥0 → Ω → E) (T : ℝ≥0) (q : ℕ → Set.Iic T) (hq : DenseRange q)
    (ω : Ω) (hc : Continuous (fun t ↦ X t ω)) :
    Tendsto (fun n ↦ (sampleSet T q n).sup' (sampleSet_nonempty T q n)
      (fun t ↦ ‖X t ω‖)) atTop (𝓝 (pathSup X T ω)) := by
  let f : ℕ → ℝ := fun n ↦ (sampleSet T q n).sup' (sampleSet_nonempty T q n)
    (fun t ↦ ‖X t ω‖)
  have hb := norm_range_bddAbove X T ω hc
  have hble : ∀ n, f n ≤ pathSup X T ω := by
    intro n
    apply Finset.sup'_le
    intro t ht
    exact le_ciSup hb ⟨t, sampleSet_le T q n ht⟩
  have hbf : BddAbove (Set.range f) := ⟨pathSup X T ω, by
    rintro _ ⟨n,rfl⟩; exact hble n⟩
  have hm : Monotone f := by
    intro i j hij
    apply Finset.sup'_le
    intro t ht
    exact Finset.le_sup' (f := fun t ↦ ‖X t ω‖) (sampleSet_monotone T q hij ht)
  have hd : (⨆ k, ‖X (q k).val ω‖) = pathSup X T ω := by
    have h := hq.ciSup' (hc.norm.comp continuous_subtype_val)
    have heq : (⨆ s : Set.range q, ‖X s.val.val ω‖) = (⨆ k, ‖X (q k).val ω‖) := by
      change sSup _ = sSup _
      congr 1
      ext y
      constructor
      · rintro ⟨⟨t,⟨k,rfl⟩⟩,rfl⟩
        exact ⟨k,rfl⟩
      · rintro ⟨k,rfl⟩
        exact ⟨⟨q k,⟨k,rfl⟩⟩,rfl⟩
    exact heq.symm.trans h
  have he : (⨆ n, f n) = pathSup X T ω := by
    apply le_antisymm
    · exact ciSup_le hble
    · rw [← hd]
      apply ciSup_le
      intro k
      apply le_trans _ (le_ciSup hbf (k+1))
      apply Finset.le_sup' (f := fun t ↦ ‖X t ω‖)
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩)
  rw [← he]
  exact tendsto_atTop_ciSup hm hbf

/-- Strong continuous-time L² Doob bound, proved from finite ordered samples
and Fatou; no continuous-time strong maximal inequality is assumed. -/
theorem pathSup_eLpNorm_le {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}
    (hX : Martingale X 𝓕 μ) (hc : ∀ ω, Continuous (fun t ↦ X t ω)) (T : ℝ≥0) :
    eLpNorm (pathSup X T) 2 μ ≤ 2 * eLpNorm (X T) 2 μ := by
  letI : Nonempty (Set.Iic T) := ⟨⟨T, show T ≤ T from le_rfl⟩⟩
  let q := TopologicalSpace.denseSeq (Set.Iic T)
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq _
  let f : ℕ → Ω → ℝ := fun n ω ↦ (sampleSet T q n).sup' (sampleSet_nonempty T q n)
    (fun t ↦ ‖X t ω‖)
  apply Lp.eLpNorm_le_of_ae_tendsto (f:=f) (u:=atTop)
  · exact Filter.Eventually.of_forall fun n ↦ by
      simpa only [f, sampleSet_max] using
        finite_max_eLpNorm_le hX (sampleSet T q n) (sampleSet_nonempty T q n)
  · intro n
    apply Measurable.aestronglyMeasurable
    convert (Finset.measurable_sup' (sampleSet_nonempty T q n)
      (fun t _ ↦ ((hX.stronglyAdapted t).mono (𝓕.le t)).norm.measurable)) using 1
    funext ω
    exact (Finset.sup'_apply (sampleSet_nonempty T q n) (fun t ω ↦ ‖X t ω‖) ω).symm
  · exact ae_of_all _ fun ω ↦ sampled_max_tendsto X T q hq ω (hc ω)


/-- The pathwise full supremum is measurable as a limit of finite measurable
maxima; no uncountable-supremum measurability is assumed. -/
theorem pathSup_aestronglyMeasurable {Ω E : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}
    (hX : StronglyAdapted 𝓕 X) (hc : ∀ ω, Continuous (fun t ↦ X t ω)) (T : ℝ≥0) :
    AEStronglyMeasurable (pathSup X T) μ := by
  letI : Nonempty (Set.Iic T) := ⟨⟨T, show T ≤ T from le_rfl⟩⟩
  let q := TopologicalSpace.denseSeq (Set.Iic T)
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq _
  let f : ℕ → Ω → ℝ := fun n ω ↦ (sampleSet T q n).sup' (sampleSet_nonempty T q n)
    (fun t ↦ ‖X t ω‖)
  apply aestronglyMeasurable_of_tendsto_ae (f:=f) atTop
  · intro n
    apply Measurable.aestronglyMeasurable
    convert (Finset.measurable_sup' (sampleSet_nonempty T q n)
      (fun t _ ↦ ((hX t).mono (𝓕.le t)).norm.measurable)) using 1
    funext ω
    exact (Finset.sup'_apply (sampleSet_nonempty T q n) (fun t ω ↦ ‖X t ω‖) ω).symm
  · exact ae_of_all _ fun ω ↦ sampled_max_tendsto X T q hq ω (hc ω)

/-- Every continuous square-integrable-terminal martingale is genuinely S². -/
theorem pathSup_memLp {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}
    (hX : Martingale X 𝓕 μ) (hc : ∀ ω, Continuous (fun t ↦ X t ω)) (T : ℝ≥0)
    (hT : MemLp (X T) 2 μ) : MemLp (pathSup X T) 2 μ := by
  refine ⟨pathSup_aestronglyMeasurable hX.stronglyAdapted hc T, ?_⟩
  exact (pathSup_eLpNorm_le hX hc T).trans_lt
    (ENNReal.mul_lt_top (by norm_num) hT.eLpNorm_lt_top)

/-- In particular the actual square of the whole-interval path supremum has
finite Bochner expectation. -/
theorem integrable_pathSup_sq {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {𝓕 : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}
    (hX : Martingale X 𝓕 μ) (hc : ∀ ω, Continuous (fun t ↦ X t ω)) (T : ℝ≥0)
    (hT : MemLp (X T) 2 μ) : Integrable (fun ω ↦ pathSup X T ω ^ 2) μ :=
  (pathSup_memLp hX hc T hT).integrable_sq

end LinearStochastic.ContinuousDoobL2

