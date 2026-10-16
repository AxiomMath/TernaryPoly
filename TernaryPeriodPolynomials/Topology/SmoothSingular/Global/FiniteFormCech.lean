module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteCofaces
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteFamilies
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechOperators

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Manifold ContDiff

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- A nonzero actual equivariant form has a nonempty actual quotient domain. -/
theorem equivariantForm_domain_nonempty {U : Set OrbitSpace} {n : ℕ}
    (w : EquivariantForm ρ U n) (hw : w ≠ 0) : U.Nonempty := by
  by_contra h
  apply hw
  apply Subtype.ext
  apply Form.ext
  intro x hx
  exact (h ⟨coordinateProjection x,hx.2⟩).elim

variable (C : CompactConvexCover)

/-- Every actual face restriction preserves finite tuple support for the locally finite
compact-closure cover. This uses the genuine nonempty-coface finiteness theorem. -/
theorem formCechSelect_finiteSupport (n k : ℕ) (a : Fin (k+2))
    (w : FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) n (k+1))
    (hw : (familySupport w).Finite) :
    (familySupport (formCechSelect ρ (fun i => (C.sheet i).quotientDomain) n a.succAbove w)).Finite := by
  apply (C.finite_cofaces k hw).subset
  intro t ht
  refine ⟨equivariantForm_domain_nonempty ρ _ ht,a,?_⟩
  intro hz
  apply ht
  change restrictEquivariant ρ (cechDomain_select_subset _ a.succAbove t) n
    (w (t ∘ a.succAbove)) = 0
  rw [hz,map_zero]

/-- The actual alternating Čech differential preserves finite tuple support. -/
theorem formCechD_finiteSupport (n k : ℕ)
    (w : FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) n (k+1))
    (hw : (familySupport w).Finite) :
    (familySupport (formCechD ρ (fun i => (C.sheet i).quotientDomain) n (k+1) w)).Finite := by
  change formCechD ρ (fun i => (C.sheet i).quotientDomain) n (k+1) w ∈
    finiteFamilySubmodule (fun t : Fin (k+2) → C.Index =>
      EquivariantForm ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t) n)
  unfold formCechD
  rw [LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro a _
  rw [LinearMap.smul_apply]
  exact (finiteFamilySubmodule (fun t : Fin (k+2) → C.Index =>
    EquivariantForm ρ (cechDomain (fun i => (C.sheet i).quotientDomain) t) n)).toAddSubgroup.zsmul_mem
      (formCechSelect_finiteSupport ρ C n k a w hw) _

/-- The literal exterior derivative preserves finite tuple support componentwise. -/
theorem formCechVertical_finiteSupport (n k : ℕ)
    (w : FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) n k)
    (hw : (familySupport w).Finite) :
    (familySupport (fun t => differential ρ
      (cechDomain_isOpen (fun i => (C.sheet i).quotientDomain)
        (fun i => (C.sheet i).quotientDomain_isOpen) t) n (w t))).Finite :=
  finiteFamily_map _ _ hw

/-- The actual partition homotopy preserves finite nonzero tuple support. Its support is
contained in the image under deletion of the first index of the input's finite support. -/
theorem formCechH_finiteSupport (n k : ℕ)
    (φ : SmoothPartitionOfUnity C.Index 𝓘(ℝ, Coordinates) OrbitSpace Set.univ)
    (hφ : φ.IsSubordinate (fun i => (C.sheet i).quotientDomain))
    (w : FormCechTerms ρ (fun i => (C.sheet i).quotientDomain) n (k+1))
    (hw : (familySupport w).Finite) :
    (familySupport (formCechH ρ (fun i => (C.sheet i).quotientDomain) n
      (fun i => (C.sheet i).quotientDomain_isOpen) φ hφ k w)).Finite := by
  apply (hw.image (fun t => fun i : Fin k => t i.succ)).subset
  intro t ht
  by_contra h
  have hz (i : C.Index) : w (Fin.cons i t) = 0 := by
    by_contra hn
    apply h
    exact ⟨Fin.cons i t,hn,by funext j; simp⟩
  apply ht
  change partitionSumLinear _ _ _ _ _ _ (formCechPrefix ρ _ n k t w) = 0
  have hp : formCechPrefix ρ (fun i => (C.sheet i).quotientDomain) n k t w = 0 := by
    funext i
    change restrictEquivariant ρ (cechDomain_subset_cons _ i t) n (w (Fin.cons i t)) = 0
    rw [hz,map_zero]
  rw [hp,map_zero]

end TernaryPoly.SmoothSingularGlobal
