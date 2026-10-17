module

public import LinearStochastic.CommonLocalS2Bound
public import LinearStochastic.CommonForwardGlobalBound

@[expose] public section

/-! Coefficient-only full-path S² estimates on every finite horizon, by
literal prefix/restart of the same actual solution on a genuine finite mesh. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace LinearStochastic.CommonGlobalS2Bound
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators
open CommonVectorPicard CommonLocalSolution CommonSolutionData CommonLocalS2Bound
open CommonHorizonRestriction CommonSolutionRestriction CommonShiftH2 CommonShiftSimple

def meshBound (K : ℝ) : ℕ → ℝ
  | 0=>1
  | n+1=>meshBound K n+K*(meshBound K n+1)

theorem meshBound_nonneg {K : ℝ} (hK : 0≤K) (N : ℕ) : 0 ≤ meshBound K N := by
  induction N with
  | zero=>exact zero_le_one
  | succ N ih=>exact add_nonneg ih (mul_nonneg hK (add_nonneg ih zero_le_one))

/-- An explicit constant depending only on the horizon and deterministic
coefficient matrices. Its definition has no probability space or driver input. -/
def boundConstant {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ) : ℝ :=
  let N := Classical.choose (CommonUniformHorizon.exists_mesh T A C)
  meshBound (localBound (T/(N:ℝ≥0)) A B C D) N

theorem boundConstant_nonneg {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (T : ℝ≥0) (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ)
    (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ) :
    0 ≤ boundConstant T A B C D := by
  exact meshBound_nonneg (zero_le_one.trans (localBound_ge_one _ A B C D
    (Classical.choose_spec (CommonUniformHorizon.exists_mesh T A C)).2)) _

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {𝓕 : Filtration ℝ≥0 mΩ} [𝓕.IsComplete μ]
  {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  {W : ι → ℝ≥0 → Ω → ℝ}
  [∀ i, CommonItoIsometry.ForwardIndependent (W i) 𝓕 μ]
  (hW : ∀ i, IsPreBrownianReal (W i) μ) (hWm : ∀ i t, Measurable (W i t))
  (hWc : ∀ i ω, Continuous fun t=>W i t ω)

include hWc in
/-- All finite-mesh prefixes of the same actual solution satisfy a full-path
estimate. There is no assumption about a supremum in the induction hypothesis. -/
theorem grid_bound (i₀ : ι) (δ : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (hb : CommonUniformHorizon.bound δ A C<1)
    (ξ : κ → Ω → ℝ) (_hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) :
    ∀ N : ℕ, ∀ u : ν → H2 𝓕 μ ((N:ℝ≥0)*δ),
      ∀ q : Solution hW hWm ((N:ℝ≥0)*δ) A B C D ξ u, ∀ b : κ,
      PathSupNorm.norm (μ:=μ) (q.path b) ((N:ℝ≥0)*δ) ≤
        meshBound (localBound δ A B C D) N*(‖fun b=>(hξ2 b).toLp (ξ b)‖+‖u‖) := by
  intro N
  induction N with
  | zero=>
    intro u q b
    have he : ∀ᵐ ω ∂μ, ∀ t, t≤((0:ℕ):ℝ≥0)*δ → q.path b t ω=ξ b ω := by
      filter_upwards [q.initial b] with ω hω
      intro t ht
      have ht0 : t=0 := by simpa only [Nat.cast_zero,zero_mul,le_zero_iff] using ht
      simpa only [ht0] using hω
    rw [PathSupNorm.congr _ he,PathSupNorm.constant _ (ξ b) (hξ2 b),meshBound,one_mul]
    exact (norm_le_pi_norm (fun b=>(hξ2 b).toLp (ξ b)) b).trans (le_add_of_nonneg_right (norm_nonneg _))
  | succ N ih=>
    have htime : ((N+1:ℕ):ℝ≥0)*δ=(N:ℝ≥0)*δ+δ := by push_cast; ring
    rw [htime]
    intro u q b
    let a : ℝ≥0 := (N:ℝ≥0)*δ
    have ha : a≤a+δ := le_add_right le_rfl
    let up := fun c=>restriction (hWm i₀) ha (u c)
    let qp := prefixSolution hW hWm i₀ a (a+δ) ha A B C D ξ u q
    let qs := shifted hW hWm a δ (a+δ) le_rfl A B C D ξ u q
    have hK : 0≤localBound δ A B C D := zero_le_one.trans (localBound_ge_one δ A B C D hb)
    have hM := meshBound_nonneg hK N
    have hup : ‖up‖≤‖u‖ := by
      have hh := CommonForwardGlobalBound.pi_contraction (restriction (hWm i₀) ha)
        (CommonForwardGlobalBound.restriction_norm hWm i₀ ha) u 0
      have hz : (fun b=>restriction (hWm i₀) ha ((0:ν→H2 𝓕 μ (a+δ)) b))=0 := by
        funext b
        exact map_zero _
      rw [hz,sub_zero,sub_zero] at hh
      exact hh
    have hpre (c : κ) : PathSupNorm.norm (μ:=μ) (q.path c) a ≤
        meshBound (localBound δ A B C D) N*(‖fun b=>(hξ2 b).toLp (ξ b)‖+‖u‖) :=
      (ih up qp c).trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hup) hM)
    have hF0 : 𝓕 a≤CommonTimeShift.filtration 𝓕 a 0 := by
      change 𝓕 a≤𝓕 (a+0)
      rw [add_zero]
    have hstart (c : κ) : StronglyMeasurable[CommonTimeShift.filtration 𝓕 a 0] (q.path c a) :=
      ((q.progressive c).isStronglyProgressive.stronglyAdapted a).mono hF0
    have hstart2 (c : κ) : MemLp (q.path c a) 2 μ := (endpoint_memLp hW hWm a A B C D ξ up qp c).2
    have hinit : ‖fun c=>(hstart2 c).toLp (q.path c a)‖ ≤
        meshBound (localBound δ A B C D) N*(‖fun b=>(hξ2 b).toLp (ξ b)‖+‖u‖) := by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM (add_nonneg (norm_nonneg _) (norm_nonneg _)))).mpr
      intro c
      rw [Lp.norm_toLp]
      exact (PathSupNorm.eval_le a a le_rfl (q.path c) (qp.continuous c) (qp.squareSup c)).trans (hpre c)
    have hshift : ‖fun c=>shiftCLM a δ (a+δ) le_rfl (u c)‖≤‖u‖ := by
      have hh := CommonForwardGlobalBound.pi_contraction
        (shiftCLM (𝓕:=𝓕) (μ:=μ) a δ (a+δ) le_rfl) (shift_norm a δ (a+δ) le_rfl) u 0
      have hz : (fun b=>shiftCLM a δ (a+δ) le_rfl ((0:ν→H2 𝓕 μ (a+δ)) b))=0 := by
        funext b
        exact map_zero _
      rw [hz,sub_zero,sub_zero] at hh
      exact hh
    have hfuture := CommonLocalS2Bound.local_bound (𝓕:=CommonTimeShift.filtration 𝓕 a)
      (fun i=>CommonTimeShift.preBrownian (hW i) a) (fun i=>shiftedMeas (hWm i) a)
      (fun i=>CommonTimeShift.continuous_driver (hWc i) a) i₀ δ A B C D
      (fun c=>q.path c a) hstart hstart2 (fun c=>shiftCLM a δ (a+δ) le_rfl (u c)) qs hb b
    have hf := hfuture.trans (mul_le_mul_of_nonneg_left (add_le_add hinit hshift) hK)
    have hs := PathSupNorm.split_le a δ (q.path b) (qp.continuous b) (qs.continuous b)
      (qp.squareSup b) (qs.squareSup b)
    apply (hs.trans (add_le_add (hpre b) hf)).trans
    rw [meshBound]
    have hI := norm_nonneg (fun b=>(hξ2 b).toLp (ξ b))
    nlinarith [mul_nonneg hK hI]

include hWc in
/-- The actual bound holds with the explicitly coefficient-only constant. -/
theorem explicit_bound (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T)
    (q : Solution hW hWm T A B C D ξ u) (b : κ) :
    PathSupNorm.norm (μ:=μ) (q.path b) T ≤ boundConstant T A B C D*
      (‖fun b=>(hξ2 b).toLp (ξ b)‖+‖u‖) := by
  let N := Classical.choose (CommonUniformHorizon.exists_mesh T A C)
  have hh := Classical.choose_spec (CommonUniformHorizon.exists_mesh T A C)
  have hne : (N:ℝ≥0)≠0 := by exact_mod_cast Nat.ne_of_gt hh.1
  have he : (N:ℝ≥0)*(T/(N:ℝ≥0))=T := mul_div_cancel₀ T hne
  have hb := grid_bound hW hWm hWc i₀ (T/(N:ℝ≥0)) A B C D hh.2 ξ hξ hξ2 N
  rw [he] at hb
  exact hb u q b

include hWc in
/-- A coefficient-only full-path S² bound on each prescribed finite horizon,
for every actual solution, initial random variable and control. -/
theorem full_bound (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ) :
    ∃ K : ℝ, 0≤K ∧ ∀ (ξ : κ → Ω → ℝ) (_hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
      (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T)
      (q : Solution hW hWm T A B C D ξ u), ∀ b,
      PathSupNorm.norm (μ:=μ) (q.path b) T ≤ K*(‖fun b=>(hξ2 b).toLp (ξ b)‖+‖u‖) := by
  obtain ⟨N,hN,hb⟩ := CommonUniformHorizon.exists_mesh T A C
  let δ := T/(N:ℝ≥0)
  have hne : (N:ℝ≥0)≠0 := by exact_mod_cast Nat.ne_of_gt hN
  have he : (N:ℝ≥0)*δ=T := mul_div_cancel₀ T hne
  refine ⟨meshBound (localBound δ A B C D) N,
    meshBound_nonneg (zero_le_one.trans (localBound_ge_one δ A B C D hb)) N,?_⟩
  intro ξ hξ hξ2
  have hh := grid_bound hW hWm hWc i₀ δ A B C D hb ξ hξ hξ2 N
  rw [he] at hh
  exact hh

/-- Original Brownian paths satisfy the same explicit coefficient-only
constant, since repaired-driver transport leaves their actual paths unchanged. -/
theorem brownian_explicit_bound (hB : ∀ i, IsBrownianReal (W i) μ) (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ)
    (ξ : κ → Ω → ℝ) (hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
    (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T)
    (q : Solution (fun i=>(hB i).toIsPreBrownianReal) hWm T A B C D ξ u) (b : κ) :
    PathSupNorm.norm (μ:=μ) (q.path b) T ≤ boundConstant T A B C D*
      (‖fun b=>(hξ2 b).toLp (ξ b)‖+‖u‖) := by
  have he (i : ι) : ∀ᵐ ω ∂μ, ∀ t,W i t ω=CommonBrownianRepair.repaired hB i t ω :=
    (hB i).mk_ae_forall_eq.mono (fun _ hω t=>(hω t).symm)
  let q' := CommonBrownianGlobal.change_driver (fun i=>(hB i).toIsPreBrownianReal)
    (fun i=>(CommonBrownianRepair.repaired_brownian hB i).toIsPreBrownianReal)
    hWm (CommonBrownianRepair.repaired_measurable hB) he T A B C D ξ u q
  exact explicit_bound (𝓕:=𝓕)
    (fun i=>(CommonBrownianRepair.repaired_brownian hB i).toIsPreBrownianReal)
    (CommonBrownianRepair.repaired_measurable hB) (CommonBrownianRepair.repaired_continuous hB)
    i₀ T A B C D ξ hξ hξ2 u q' b

/-- Original Brownian drivers require no everywhere-continuity assumption;
proved driver transport leaves the full actual paths unchanged. -/
theorem brownian_full_bound (hB : ∀ i, IsBrownianReal (W i) μ) (i₀ : ι) (T : ℝ≥0)
    (A : Matrix κ κ ℝ) (B : Matrix κ ν ℝ) (C : ι → Matrix κ κ ℝ) (D : ι → Matrix κ ν ℝ) :
    ∃ K : ℝ, 0≤K ∧ ∀ (ξ : κ → Ω → ℝ) (_hξ : ∀ b, StronglyMeasurable[𝓕 0] (ξ b))
      (hξ2 : ∀ b, MemLp (ξ b) 2 μ) (u : ν → H2 𝓕 μ T)
      (q : Solution (fun i=>(hB i).toIsPreBrownianReal) hWm T A B C D ξ u), ∀ b,
      PathSupNorm.norm (μ:=μ) (q.path b) T ≤ K*(‖fun b=>(hξ2 b).toLp (ξ b)‖+‖u‖) := by
  obtain ⟨K,hK,hbound⟩ := full_bound (𝓕:=𝓕)
    (fun i=>(CommonBrownianRepair.repaired_brownian hB i).toIsPreBrownianReal)
    (CommonBrownianRepair.repaired_measurable hB) (CommonBrownianRepair.repaired_continuous hB)
    i₀ T A B C D
  refine ⟨K,hK,?_⟩
  intro ξ hξ hξ2 u q
  have he (i : ι) : ∀ᵐ ω ∂μ, ∀ t,W i t ω=CommonBrownianRepair.repaired hB i t ω :=
    (hB i).mk_ae_forall_eq.mono (fun _ hω t=>(hω t).symm)
  let q' := CommonBrownianGlobal.change_driver (fun i=>(hB i).toIsPreBrownianReal)
    (fun i=>(CommonBrownianRepair.repaired_brownian hB i).toIsPreBrownianReal)
    hWm (CommonBrownianRepair.repaired_measurable hB) he T A B C D ξ u q
  exact hbound ξ hξ hξ2 u q'

end LinearStochastic.CommonGlobalS2Bound
