module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.SmallCochains
public import TernaryPeriodPolynomials.Topology.SingularHomology.MayerVietorisSES

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantSingularMayerVietoris
open CategoryTheory Limits FreeActionLinearization EquivariantSingularResolution EquivariantSingularSmall
open SphereOddDegree TopologicalSpace

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]

/-- Actual subordinate-chain inclusion between nested invariant subsets. -/
def subordinateMap (S T : Set E) (hS : InvariantSet G E S) (hT : InvariantSet G E T) (hST : S ⊆ T) :
    subordinateComplex G E S hS ⟶ subordinateComplex G E T hT :=
  familyMap G E (fun _ => IsSubordinate S) (subordinate_invariant G E S hS)
    (fun n => singularBoundary_maps_subChainSubmodule (R := ℚ) (X := E) (S := S) n)
    (fun _ => IsSubordinate T) (subordinate_invariant G E T hT)
    (fun n => singularBoundary_maps_subChainSubmodule (R := ℚ) (X := E) (S := T) n)
    (fun _ _ hσ => hσ.mono hST)

/-- Actual inclusion from chains in one invariant cover member into its small-chain complex. -/
def subordinateToSmall (𝒰 : OpenCoverData E) (h𝒰 : InvariantCover G E 𝒰)
    (S : Set E) (hS : InvariantSet G E S) (hmem : S ∈ 𝒰.sets) :
    subordinateComplex G E S hS ⟶ smallComplex G E 𝒰 h𝒰 :=
  familyMap G E (fun _ => IsSubordinate S) (subordinate_invariant G E S hS)
    (fun n => singularBoundary_maps_subChainSubmodule (R := ℚ) (X := E) (S := S) n)
    (fun _ => IsSmallSimplex 𝒰) (small_invariant G E 𝒰 h𝒰)
    (fun n => singularBoundary_maps_smallChainSubmodule (R := ℚ) (X := E) (𝒰 := 𝒰) n)
    (fun _ _ hσ => hσ.isSmallSimplex hmem)

omit [ContinuousConstSMul G E] in
/-- Intersections of actual invariant subsets are invariant. -/
theorem invariant_inter (S T : Set E) (hS : InvariantSet G E S) (hT : InvariantSet G E T) :
    InvariantSet G E (S ∩ T) := fun g x hx => ⟨hS g x hx.1,hT g x hx.2⟩

variable (U V : Opens E) (hU : InvariantSet G E (U : Set E)) (hV : InvariantSet G E (V : Set E))
  (hUV : U ⊔ V = ⊤)

omit [ContinuousConstSMul G E] in
include hU hV in
/-- The actual two-set open cover is invariant when both open sets are invariant. -/
theorem twoSetCover_invariant : InvariantCover G E (twoSetCover U V hUV) := by
  rintro S (rfl | rfl)
  · exact hU
  · exact hV

/-- Actual equivariant chains subordinate to the entire intersection. -/
abbrev interChains := subordinateComplex G E ((U : Set E) ∩ (V : Set E)) (invariant_inter G E _ _ hU hV)

/-- Actual equivariant chains subordinate to the left open set. -/
abbrev leftChains := subordinateComplex G E (U : Set E) hU

/-- Actual equivariant chains subordinate to the right open set. -/
abbrev rightChains := subordinateComplex G E (V : Set E) hV

/-- Actual equivariant small chains for the full two-set cover. -/
abbrev coverChains := smallComplex G E (twoSetCover U V hUV) (twoSetCover_invariant G E U V hU hV hUV)

/-- The actual intersection inclusion into the left subordinate chains. -/
def interToLeft : interChains G E U V hU hV ⟶ leftChains G E U hU :=
  subordinateMap G E _ _ (invariant_inter G E _ _ hU hV) hU Set.inter_subset_left

/-- The actual intersection inclusion into the right subordinate chains. -/
def interToRight : interChains G E U V hU hV ⟶ rightChains G E V hV :=
  subordinateMap G E _ _ (invariant_inter G E _ _ hU hV) hV Set.inter_subset_right

/-- The actual left inclusion into the small chains. -/
def leftToCover : leftChains G E U hU ⟶ coverChains G E U V hU hV hUV :=
  subordinateToSmall G E (twoSetCover U V hUV) (twoSetCover_invariant G E U V hU hV hUV)
    (U : Set E) hU (twoSetCover_memU U V hUV)

/-- The actual right inclusion into the small chains. -/
def rightToCover : rightChains G E V hV ⟶ coverChains G E U V hU hV hUV :=
  subordinateToSmall G E (twoSetCover U V hUV) (twoSetCover_invariant G E U V hU hV hUV)
    (V : Set E) hV (twoSetCover_memV U V hUV)

/-- Both inclusion routes from intersection chains are literally the same chain map. -/
theorem inclusion_square :
    interToLeft G E U V hU hV ≫ leftToCover G E U V hU hV hUV =
      interToRight G E U V hU hV ≫ rightToCover G E U V hU hV hUV := by
  apply HomologicalComplex.hom_ext
  intro n
  ext c
  rfl

/-- The genuine equivariant Mayer–Vietoris left map, with signs `(c,-c)`. -/
def leftMap : interChains G E U V hU hV ⟶ leftChains G E U hU ⊞ rightChains G E V hV :=
  biprod.lift (interToLeft G E U V hU hV) (-(interToRight G E U V hU hV))

/-- The genuine equivariant Mayer–Vietoris right map, the sum of actual inclusions. -/
def rightMap : leftChains G E U hU ⊞ rightChains G E V hV ⟶ coverChains G E U V hU hV hUV :=
  biprod.desc (leftToCover G E U V hU hV hUV) (rightToCover G E U V hU hV hUV)

/-- The actual signed equivariant Mayer–Vietoris maps compose to zero. -/
theorem leftMap_comp_rightMap : leftMap G E U V hU hV ≫ rightMap G E U V hU hV hUV = 0 := by
  rw [leftMap, rightMap, biprod.lift_desc, inclusion_square G E U V hU hV hUV]
  simp only [Preadditive.neg_comp, add_neg_cancel]

/-- The actual equivariant Mayer–Vietoris short complex of chain complexes. -/
def chainShortComplex : ShortComplex (ChainComplex (Rep ℚ G) ℕ) :=
  ShortComplex.mk (leftMap G E U V hU hV) (rightMap G E U V hU hV hUV)
    (leftMap_comp_rightMap G E U V hU hV hUV)

end TernaryPoly.EquivariantSingularMayerVietoris
