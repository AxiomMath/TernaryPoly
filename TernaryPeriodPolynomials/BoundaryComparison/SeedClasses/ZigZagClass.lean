module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.ZigZagAlgebra
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.Order.Fin.SuccAboveOrderIso
public import Mathlib.RingTheory.SimpleRing.Matrix

@[expose] public section


/-!
# The zig-zag class in Mathlib's group cohomology

The zig-zag cochain of `ZigZagAlgebra` is an element of `groupCohomology.cocycles₂ (Rep.of ρ)`
(Mathlib's inhomogeneous 2-cocycles, same sign convention), and its image in `H²(G, V)` does not
depend on the choices of the data.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology

namespace TernaryPeriodPolynomials.Argument.SeedC3.ZigZag

universe u

variable {k : Type u} [CommRing k] {G : Type u} [Group G]
  {V Ω0 Ω1 Ω2 : Type u} [AddCommGroup V] [Module k V] [AddCommGroup Ω0] [Module k Ω0]
  [AddCommGroup Ω1] [Module k Ω1] [AddCommGroup Ω2] [Module k Ω2]
  {ρ : Representation k G V} {d0 : Ω0 →ₗ[k] Ω1} {d1 : Ω1 →ₗ[k] Ω2}
  {P0 : G → Ω0 →ₗ[k] Ω0} {P1 : G → Ω1 →ₗ[k] Ω1} {P2 : G → Ω2 →ₗ[k] Ω2}
  {T0 : G → Ω0 →ₗ[k] Ω0} {T1 : G → Ω1 →ₗ[k] Ω1} {T2 : G → Ω2 →ₗ[k] Ω2}
  {c : V →ₗ[k] Ω0}

/-- The zig-zag cochain as a Mathlib 2-cocycle of the representation `ρ`. -/
noncomputable def cochainCocycle (L : Laws ρ d0 d1 P0 P1 P2 T0 T1 T2 c) {ω : Ω2}
    (D : Datum d0 d1 P1 T1 ω) : cocycles₂ (Rep.of ρ) :=
  ⟨fun p => cochain L D p.1 p.2, (mem_cocycles₂_iff _).2
    (fun g h j => cochain_isCocycle L D g h j)⟩

/-- The class of the zig-zag in `H²(G, V)`. -/
noncomputable def zigzagClass (L : Laws ρ d0 d1 P0 P1 P2 T0 T1 T2 c) {ω : Ω2}
    (D : Datum d0 d1 P1 T1 ω) : H2 (Rep.of ρ) :=
  H2π (Rep.of ρ) (cochainCocycle L D)

/-- **The class does not depend on the choices of `(η, θ)`.** -/
theorem zigzagClass_indep (L : Laws ρ d0 d1 P0 P1 P2 T0 T1 T2 c) {ω : Ω2}
    (D D' : Datum d0 d1 P1 T1 ω) : zigzagClass L D' = zigzagClass L D := by
  obtain ⟨κ, hκ⟩ := cochain_indep L D D'
  rw [← sub_eq_zero, zigzagClass, zigzagClass, ← map_sub, H2π_eq_zero_iff]
  refine ⟨κ, ?_⟩
  funext p
  simp only [d₁₂_hom_apply]
  show _ = cochain L D' p.1 p.2 - cochain L D p.1 p.2
  rw [hκ p.1 p.2]
  abel

/-- **Additivity of the class.** -/
theorem zigzagClass_add (L : Laws ρ d0 d1 P0 P1 P2 T0 T1 T2 c) {ω ω' : Ω2}
    (D : Datum d0 d1 P1 T1 ω) (D' : Datum d0 d1 P1 T1 ω') :
    zigzagClass L (D.add D') = zigzagClass L D + zigzagClass L D' := by
  unfold zigzagClass
  rw [← map_add]
  congr 1
  apply Subtype.ext
  funext p
  exact cochain_add L D D' p.1 p.2

/-- **Homogeneity of the class.** -/
theorem zigzagClass_smul (L : Laws ρ d0 d1 P0 P1 P2 T0 T1 T2 c) (a : k) {ω : Ω2}
    (D : Datum d0 d1 P1 T1 ω) : zigzagClass L (D.smul a) = a • zigzagClass L D := by
  unfold zigzagClass
  rw [← map_smul]
  congr 1
  apply Subtype.ext
  funext p
  exact cochain_smul L a D p.1 p.2

end TernaryPeriodPolynomials.Argument.SeedC3.ZigZag
