module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingCompactKernel
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering CategoryTheory
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {U V : Set OrbitSpace} (hU : IsOpen U) (hV : IsOpen V)

/-- The ordinary direct-sum complex has the actual pair of equivariant forms in each degree. -/
def ordinaryPairComplex : CochainComplex (ModuleCat ℝ) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of ℝ (EquivariantForm ρ U n × EquivariantForm ρ V n))
    (fun n => ModuleCat.ofHom ((differential ρ hU n).prodMap (differential ρ hV n))) (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro p
      exact Prod.ext (differential_squared ρ hU n p.1) (differential_squared ρ hV n p.2))

/-- Ordinary restriction as a map into the actual direct-sum complex. -/
def ordinaryUnionMap : coveringComplex ρ (hU.union hV) ⟶ ordinaryPairComplex ρ hU hV :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (unionRestriction ρ U V n)) (by
    intro n
    simp only [coveringComplex, ordinaryPairComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    exact Prod.ext (restrictEquivariant_d ρ (hU.union hV) hU subset_union_left w).symm
      (restrictEquivariant_d ρ (hU.union hV) hV subset_union_right w).symm)

/-- Ordinary restriction difference as a cochain map to the overlap complex. -/
def ordinaryOverlapMap : ordinaryPairComplex ρ hU hV ⟶ coveringComplex ρ (hU.inter hV) :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (intersectionDifference ρ U V n)) (by
    intro n
    simp only [coveringComplex, ordinaryPairComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro p
    change differential ρ (hU.inter hV) n
      (restrictEquivariant ρ inter_subset_left n p.1 - restrictEquivariant ρ inter_subset_right n p.2) =
      restrictEquivariant ρ inter_subset_left (n + 1) (differential ρ hU n p.1) -
        restrictEquivariant ρ inter_subset_right (n + 1) (differential ρ hV n p.2)
    rw [map_sub, ← restrictEquivariant_d ρ hU (hU.inter hV) inter_subset_left,
      ← restrictEquivariant_d ρ hV (hU.inter hV) inter_subset_right])

/-- The actual ordinary Mayer-Vietoris short complex. -/
def ordinarySequence : ShortComplex (CochainComplex (ModuleCat ℝ) ℕ) :=
  ShortComplex.mk (ordinaryUnionMap ρ hU hV) (ordinaryOverlapMap ρ hU hV) (by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    exact intersectionDifference_unionRestriction ρ U V n w)

/-- Short exactness of the genuine ordinary Mayer-Vietoris sequence of complexes. -/
theorem ordinarySequence_shortExact : (ordinarySequence ρ hU hV).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    intro p
    exact ordinary_kernel_exact hU hV p
  · apply (ModuleCat.mono_iff_injective _).mpr
    exact unionRestriction_injective ρ U V n
  · apply (ModuleCat.epi_iff_surjective _).mpr
    exact intersectionDifference_surjective ρ U V n hU hV

end TernaryPoly.SmoothDeRhamGluing
