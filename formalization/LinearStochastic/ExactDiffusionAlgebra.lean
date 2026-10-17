module

public import LinearStochastic.ConeBlocks
public import LinearStochastic.InputStructure
public import LinearStochastic.SectionSolutionLinearity

@[expose] public section

/-! The canonical joint-diffusion right inverse produces the literal feedback
used in the exact-terminal BSDE construction, including its actual L² maps. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LinearStochastic.ExactDiffusionAlgebra
open MeasureTheory
open scoped InnerProductSpace BigOperators
variable {E U ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U] [Fintype ι]
  (D : ι → U →L[ℝ] E)
  (hD : Function.Surjective (InputStructure.jointDiffusion (fun i => (D i).toLinearMap)))

/-- The i-th column of J=D†(DD†)⁻¹, as an actual continuous linear map. -/
def rightColumn (i : ι) : E →L[ℝ] U := by
  classical
  exact ((InputStructure.canonicalRightInverse (InputStructure.jointDiffusion (fun j => (D j).toLinearMap)) hD).comp
    (ConeBlocks.inject i)).toContinuousLinearMap

/-- Recombining all actual channel columns gives the true joint right inverse. -/
theorem rightColumn_sum (z : ι → E) (j : ι) : D j (∑ i, rightColumn D hD i (z i)) = z j := by
  classical
  let J := InputStructure.canonicalRightInverse (InputStructure.jointDiffusion (fun i => (D i).toLinearMap)) hD
  let w : PiLp 2 (fun _ : ι => E) := WithLp.toLp 2 z
  have hsum : (∑ i, rightColumn D hD i (z i)) = J w := by
    change (∑ i, J (ConeBlocks.inject i (w i))) = J w
    rw [←map_sum]
    congr 1
    exact ConeBlocks.sum_inject_project w
  rw [hsum]
  have he := LinearMap.congr_fun (InputStructure.canonicalRightInverse_right_inverse
    (InputStructure.jointDiffusion (fun i => (D i).toLinearMap)) hD) w
  exact congrArg (fun q : PiLp 2 (fun _ : ι => E) => q j) he

variable {Λ : Type*} [mΛ : MeasurableSpace Λ] {ν : Measure Λ}

/-- Genuine predictable finite-energy control assembled from actual L² state
and diffusion classes. -/
def control (C : ι → E →L[ℝ] E) (X : Lp E 2 ν) (Z : ι → Lp E 2 ν) : Lp U 2 ν :=
  ∑ i, (rightColumn D hD i).compLp (Z i-(C i).compLp X)

/-- This L² control has exactly the intended pointwise representative. -/
theorem control_ae (C : ι → E →L[ℝ] E) (X : Lp E 2 ν) (Z : ι → Lp E 2 ν) :
    control D hD C X Z =ᵐ[ν] fun ω => ∑ i, rightColumn D hD i (Z i ω-C i (X ω)) := by
  have hall : ∀ᵐ ω ∂ν, ∀ i,
      (rightColumn D hD i).compLp (Z i-(C i).compLp X) ω = rightColumn D hD i (Z i ω-C i (X ω)) := by
    rw [ae_all_iff]
    intro i
    filter_upwards [(rightColumn D hD i).coeFn_compLp (Z i-(C i).compLp X),
      Lp.coeFn_sub (Z i) ((C i).compLp X),(C i).coeFn_compLp X] with ω hj hs hc
    rw [hj,hs,Pi.sub_apply,hc]
  filter_upwards [hall,Lp.coeFn_finsetSum Finset.univ
    (fun i => (rightColumn D hD i).compLp (Z i-(C i).compLp X))] with ω hω hs
  change (∑ i, (rightColumn D hD i).compLp (Z i-(C i).compLp X)) ω = _
  rw [hs]
  simp only [Finset.sum_apply,hω]

/-- The actual original diffusion coefficients are the prescribed BSDE noise. -/
theorem diffusion_control (C : ι → E →L[ℝ] E) (X : Lp E 2 ν) (Z : ι → Lp E 2 ν) (j : ι) :
    (C j).compLp X+(D j).compLp (control D hD C X Z) = Z j := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add ((C j).compLp X) ((D j).compLp (control D hD C X Z)),
    (C j).coeFn_compLp X,(D j).coeFn_compLp (control D hD C X Z),control_ae D hD C X Z]
    with ω ha hc hd hu
  rw [ha,Pi.add_apply,hc,hd,hu,rightColumn_sum]
  abel

/-- The effective drift A−BJ C, written without any dropped noise channel. -/
def effectiveDrift (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E) : E →L[ℝ] E :=
  A-∑ i, B.comp ((rightColumn D hD i).comp (C i))

def noiseDrift (B : U →L[ℝ] E) (i : ι) : E →L[ℝ] E := B.comp (rightColumn D hD i)

/-- The original drift with the constructed control equals precisely the
linear backward drift, as an equality of actual L² classes. -/
theorem drift_control (A : E →L[ℝ] E) (B : U →L[ℝ] E) (C : ι → E →L[ℝ] E)
    (X : Lp E 2 ν) (Z : ι → Lp E 2 ν) :
    A.compLp X+B.compLp (control D hD C X Z) =
      (effectiveDrift D hD A B C).compLp X+∑ i, (noiseDrift D hD B i).compLp (Z i) := by
  have hall : ∀ᵐ ω ∂ν, ∀ i, (noiseDrift D hD B i).compLp (Z i) ω = noiseDrift D hD B i (Z i ω) := by
    rw [ae_all_iff]; exact fun i => (noiseDrift D hD B i).coeFn_compLp (Z i)
  apply Lp.ext
  filter_upwards [hall,control_ae D hD C X Z,A.coeFn_compLp X,B.coeFn_compLp (control D hD C X Z),
    (effectiveDrift D hD A B C).coeFn_compLp X,
    Lp.coeFn_add (A.compLp X) (B.compLp (control D hD C X Z)),
    Lp.coeFn_add ((effectiveDrift D hD A B C).compLp X) (∑ i, (noiseDrift D hD B i).compLp (Z i)),
    Lp.coeFn_finsetSum Finset.univ (fun i => (noiseDrift D hD B i).compLp (Z i))]
    with ω hi hu ha hb hf hl hr hs
  rw [hl,hr,Pi.add_apply,Pi.add_apply,ha,hb,hu,hf,hs]
  simp only [Finset.sum_apply]
  simp only [hi]
  simp only [effectiveDrift,noiseDrift,sub_apply,
    sum_apply,ContinuousLinearMap.comp_apply,map_sum,map_sub,Finset.sum_sub_distrib]
  abel

end LinearStochastic.ExactDiffusionAlgebra
