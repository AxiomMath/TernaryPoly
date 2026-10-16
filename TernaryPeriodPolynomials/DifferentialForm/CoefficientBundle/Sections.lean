module

public import TernaryPeriodPolynomials.DifferentialForm.CoefficientBundle.Topology

@[expose] public section


/-! Actual bundle sections and deck-equivariant coefficient-valued covering functions. -/
noncomputable section
namespace TernaryPoly.PolynomialCoefficientBundle
open PolynomialCoefficientMetric SymmetricSpacePositive SymmetricSpaceCovering
  SymmetricSpaceQuotientManifold SymmetricSpaceCharts
open Set Filter Topology Bundle Manifold
open scoped ContDiff Manifold

abbrev Section (n : ℕ) := (b : OrbitSpace) → Fiber n b

def sectionMap (n : ℕ) (s : Section n) (b : OrbitSpace) : Total n := ⟨b,s b⟩

@[simp] theorem sectionMap_projection (n : ℕ) (s : Section n) (b : OrbitSpace) :
    (sectionMap n s b).proj = b := rfl

def sectionFunction (n : ℕ) (s : Section n) (S : Space) : Coefficients n :=
  coefficientAction n (deckBetween (chosenLift (quotientProjection S)) S) (s (quotientProjection S))

def IsEquivariantFunction (n : ℕ) (f : Space → Coefficients n) : Prop :=
  ∀ (g : DeckGroup) (S : Space), f (g • S) = coefficientAction n g (f S)

theorem sectionFunction_equivariant (n : ℕ) (s : Section n) : IsEquivariantFunction n (sectionFunction n s) := by
  change OrbitSpace → Coefficients n at s
  intro g S
  have hd : deckBetween (chosenLift (quotientProjection S)) (g • S) =
      g * deckBetween (chosenLift (quotientProjection S)) S := by
    apply deckBetween_unique
    rw [mul_smul, deckBetween_spec _ _ (chosenLift_projection _).symm]
  change coefficientAction n (deckBetween (chosenLift (quotientProjection (g • S))) (g • S))
    (s (quotientProjection (g • S))) =
      coefficientAction n g (coefficientAction n (deckBetween (chosenLift (quotientProjection S)) S) (s (quotientProjection S)))
  rw [quotientProjection_quotientCovering.map_smul, hd, coefficientAction_mul]

def functionSection (n : ℕ) (f : Space → Coefficients n) : Section n := fun b => f (chosenLift b)

@[simp] theorem functionSection_sectionFunction (n : ℕ) (s : Section n) :
    functionSection n (sectionFunction n s) = s := by
  change OrbitSpace → Coefficients n at s
  funext b
  simp only [functionSection, sectionFunction, chosenLift_projection, deckBetween_self, coefficientAction_one]
  rfl

theorem sectionFunction_functionSection (n : ℕ) (f : Space → Coefficients n) (hf : IsEquivariantFunction n f) :
    sectionFunction n (functionSection n f) = f := by
  funext S
  have h := hf (deckBetween (chosenLift (quotientProjection S)) S) (chosenLift (quotientProjection S))
  rw [deckBetween_spec _ _ (chosenLift_projection _).symm] at h
  exact h.symm

def equivariantFunctions (n : ℕ) : Submodule ℝ (Space → Coefficients n) where
  carrier := {f | IsEquivariantFunction n f}
  zero_mem' := by intro g S; simp
  add_mem' := by
    intro f h hf hh g S
    simpa only [Pi.add_apply, map_add] using congrArg₂ (· + ·) (hf g S) (hh g S)
  smul_mem' := by
    intro r f hf g S
    simpa only [Pi.smul_apply, map_smul] using congrArg (r • ·) (hf g S)

def sectionToEquivariant (n : ℕ) : Section n →ₗ[ℝ] equivariantFunctions n where
  toFun s := ⟨sectionFunction n s, sectionFunction_equivariant n s⟩
  map_add' s t := by apply Subtype.ext; funext S; exact map_add (coefficientAction n _) _ _
  map_smul' r s := by apply Subtype.ext; funext S; exact map_smul (coefficientAction n _) r _

def equivariantToSection (n : ℕ) : equivariantFunctions n →ₗ[ℝ] Section n where
  toFun f := functionSection n f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sectionEquivariantEquiv (n : ℕ) : Section n ≃ₗ[ℝ] equivariantFunctions n :=
  LinearEquiv.ofLinearMap (sectionToEquivariant n) (equivariantToSection n)
    (LinearMap.ext (fun f => Subtype.ext (sectionFunction_functionSection n f.val f.property)))
    (LinearMap.ext (functionSection_sectionFunction n))

def IsSmoothSection (n : ℕ) (s : Section n) : Prop :=
  ContMDiff 𝓘(ℝ, Coordinates) (𝓘(ℝ, Coordinates).prod 𝓘(ℝ, Coefficients n)) ∞ (sectionMap n s)

theorem sectionFunction_chart (n : ℕ) (s : Section n) (S R : Space)
    (hR : R ∈ (localLift S).target) :
    sectionFunction n s R = (chart n S (sectionMap n s (quotientProjection R))).2 := by
  rw [chart_apply]
  change coefficientAction n (deckBetween (chosenLift (quotientProjection R)) R) _ =
    coefficientAction n (deckBetween (chosenLift (quotientProjection R)) (localLift S (quotientProjection R))) _
  rw [localLift_projection S R hR]
  rfl

theorem smooth_sectionFunction (n : ℕ) (s : Section n) (hs : IsSmoothSection n s) :
    ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coefficients n) ∞ (sectionFunction n s) := by
  intro S
  have hq := ((chart n S).contMDiffAt_section_iff (IB := 𝓘(ℝ, Coordinates))
    (self_mem_localLift S)).mp (hs (quotientProjection S))
  have h := hq.comp S (quotientProjection_contMDiff S)
  apply h.congr_of_eventuallyEq
  have hm : S ∈ (localLift S).target := by
    simpa only [localLift_self] using (localLift S).map_source (self_mem_localLift S)
  filter_upwards [(localLift S).open_target.mem_nhds hm] with R hR
  exact sectionFunction_chart n s S R hR

theorem functionSection_chart (n : ℕ) (f : Space → Coefficients n) (hf : IsEquivariantFunction n f)
    (S : Space) {b : OrbitSpace} (hb : b ∈ (localLift S).source) :
    (chart n S (sectionMap n (functionSection n f) b)).2 = f (localLift S b) := by
  rw [chart_apply]
  have h := hf (deckBetween (chosenLift b) (localLift S b)) (chosenLift b)
  rw [deckBetween_spec _ _ ((projection_localLift S hb).trans (chosenLift_projection b).symm)] at h
  exact h.symm

theorem smooth_functionSection (n : ℕ) (f : Space → Coefficients n) (hf : IsEquivariantFunction n f)
    (hs : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coefficients n) ∞ f) :
    IsSmoothSection n (functionSection n f) := by
  intro b
  let S := chosenLift b
  have hb : b ∈ (localLift S).source := (bundleCore n).mem_baseSet_at b
  apply ((chart n S).contMDiffAt_section_iff (IB := 𝓘(ℝ, Coordinates)) hb).mpr
  have h := (hs.comp_contMDiffOn (localLift_contMDiffOn S)).contMDiffAt
    ((localLift S).open_source.mem_nhds hb)
  apply h.congr_of_eventuallyEq
  filter_upwards [(localLift S).open_source.mem_nhds hb] with c hc
  exact functionSection_chart n f hf S hc

theorem smooth_section_iff (n : ℕ) (s : Section n) :
    IsSmoothSection n s ↔ ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ, Coefficients n) ∞ (sectionFunction n s) := by
  refine ⟨smooth_sectionFunction n s, fun h => ?_⟩
  have hs := smooth_functionSection n (sectionFunction n s) (sectionFunction_equivariant n s) h
  simpa only [functionSection_sectionFunction] using hs

end TernaryPoly.PolynomialCoefficientBundle
