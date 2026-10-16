module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.PlusGroup
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlusSpecial

@[expose] public section


/-!
# The edge of `Λ₁⁺` with Levi quotient `SL(2, ℤ)` and its comparison with the good-line edge (LS12)

Line mirror of `SeedC3S4c.PlusEdge` and `PlusSpecial`.  The extension `ℤ² → Λ₁⁺ → SL(2, ℤ)` (`linePlusExtensionS`), its edge `linePlusEdgeS`
(injective since `H²` of every complex representation of `SL₂(ℤ)` vanishes), the coordinate isomorphism of its radical cohomology with
`modularBinaryRep (n+1) 0` (`linePlusRadicalCoordinateIso`, from `lowerRadicalH1Coordinate`), and the comparison `linePlusEdge_restrict`: the `Λ₁⁺`-edge of the restriction of a
relative `Λ₁`-cocycle is the `SL₂(ℤ)`-restriction of the library's good-line edge `goodLineBinaryEdge` of its class.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein Matrix CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Spectral.ModularH2
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension
open TernaryPeriodPolynomials.Argument.SeedC3S4c (SL2Z sl2zToSpecial specialToSL2Z sl2zToSpecial_injective
  sl2zToSpecial_specialToSL2Z)

/-- The coefficient representation of `Λ₁⁺` (restriction of the library's `Λ₁`-representation). -/
abbrev linePlusRep (n : ℕ) : Rep ℂ Lam1Plus := Rep.res Lam1Plus.subtype (goodLineCoefficientRep n)

/-- The Levi projection `Λ₁⁺ → SL(2, ℤ)`. -/
def linePlusProjS : Lam1Plus →* SpecialLinearGroup (Fin 2) ℤ := sl2zToSpecial.comp linePlusProj

/-- The Levi section `SL(2, ℤ) → Λ₁⁺`. -/
def linePlusSectionS : SpecialLinearGroup (Fin 2) ℤ →* Lam1Plus := linePlusSection.comp specialToSL2Z

theorem linePlusProjS_section (m : SpecialLinearGroup (Fin 2) ℤ) : linePlusProjS (linePlusSectionS m) = m := by
  change sl2zToSpecial (linePlusProj (linePlusSection (specialToSL2Z m))) = m
  rw [linePlusProj_section, sl2zToSpecial_specialToSL2Z]

/-- The split extension `ℤ² → Λ₁⁺ → SL(2, ℤ)`. -/
def linePlusExtensionS : GroupExtension RadicalLattice Lam1Plus (SpecialLinearGroup (Fin 2) ℤ) where
  inl := linePlusInl
  rightHom := linePlusProjS
  inl_injective := linePlusExtension.inl_injective
  range_inl_eq_ker_rightHom := by
    have h := linePlusExtension.range_inl_eq_ker_rightHom
    ext g
    change g ∈ linePlusInl.range ↔ sl2zToSpecial (linePlusProj g) = 1
    change linePlusInl.range = linePlusProj.ker at h
    rw [h, MonoidHom.mem_ker]
    constructor
    · intro hg
      rw [hg, map_one]
    · intro hg
      apply sl2zToSpecial_injective
      rw [hg, map_one]
  rightHom_surjective m := ⟨linePlusSectionS m, linePlusProjS_section m⟩

/-- The Levi splitting of `Λ₁⁺ → SL(2, ℤ)`. -/
def linePlusSplittingS : linePlusExtensionS.Splitting :=
  ⟨linePlusSectionS, linePlusProjS_section⟩

/-- The `(1,1)` edge of `Λ₁⁺`, Levi quotient `SL(2, ℤ)`. -/
def linePlusEdgeS (n : ℕ) :
    (twoCohomologyRestriction linePlusExtensionS.inl (linePlusRep n)).ker →ₗ[ℂ]
      groupCohomology.H1 (splitRadicalH1Representation linePlusSplittingS (linePlusRep n)) :=
  splitCohomologyEdge linePlusSplittingS (linePlusRep n)

/-- **The edge of `Λ₁⁺` is injective.** -/
theorem linePlusEdgeS_injective (n : ℕ) : Function.Injective (linePlusEdgeS n) :=
  splitCohomologyEdge_injective_of_invariant_H2_zero linePlusSplittingS (linePlusRep n)
    (fun x => modularH2_zero _ x)

theorem lineS_radicalInput (m : SpecialLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    splitRadicalInput linePlusSplittingS m r =
      splitRadicalInput goodLineSplitting (SpecialLinearGroup.toGL m) r := by
  apply goodLineRadicalInclusion_injective
  have h1 := congrArg (fun x : Lam1Plus => (x : Lam1)) (splitRadicalInput_commute linePlusSplittingS m r)
  have h2 := splitRadicalInput_commute goodLineSplitting (SpecialLinearGroup.toGL m) r
  change goodLineRadicalInclusion r * goodLineLeviSection (SpecialLinearGroup.toGL m) =
    goodLineLeviSection (SpecialLinearGroup.toGL m) *
      goodLineRadicalInclusion (splitRadicalInput linePlusSplittingS m r) at h1
  change goodLineRadicalInclusion r * goodLineLeviSection (SpecialLinearGroup.toGL m) =
    goodLineLeviSection (SpecialLinearGroup.toGL m) *
      goodLineRadicalInclusion (splitRadicalInput goodLineSplitting (SpecialLinearGroup.toGL m) r) at h2
  exact mul_left_cancel (h1.symm.trans h2)

/-- The Levi action on radical cocycles of `Λ₁⁺` is the library's lower-radical Levi action. -/
theorem lineS_cocycle_action (n : ℕ) (m : SpecialLinearGroup (Fin 2) ℤ)
    (cycle : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n)) :
    splitRadicalCocycleAction linePlusSplittingS (linePlusRep n) m cycle =
      lowerRadicalCocycleLevi n (SpecialLinearGroup.toGL m) cycle := by
  apply groupCohomology.cocycles₁_ext
  intro r
  change (linePlusRep n).ρ (linePlusSplittingS m) (cycle (splitRadicalInput linePlusSplittingS m r)) = _
  rw [lineS_radicalInput]
  exact (goodLineSplitting_cocycle_action n (SpecialLinearGroup.toGL m) cycle r).symm

theorem lineS_H1_action (n : ℕ) (m : SpecialLinearGroup (Fin 2) ℤ) :
    splitRadicalH1Action linePlusSplittingS (linePlusRep n) m =
      lowerRadicalH1Levi n (SpecialLinearGroup.toGL m) := by
  apply LinearMap.ext
  intro cohomology
  obtain ⟨cycle, rfl⟩ := oneCocycle_H1_surjective (lowerRadicalLatticeRep n) cohomology
  exact (splitRadicalH1Action_apply linePlusSplittingS (linePlusRep n) m cycle).trans
    ((congrArg (fun c : groupCohomology.cocycles₁ (lowerRadicalLatticeRep n) =>
      groupCohomology.H1π (lowerRadicalLatticeRep n) c) (lineS_cocycle_action n m cycle)).trans
      (lowerRadicalH1Levi_apply _ cycle).symm)

/-- The radical cohomology of `Λ₁⁺`, as an `SL(2, ℤ)`-representation, is `Sym^{n+1}` (twist `0`). -/
def linePlusRadicalCoordinateIso (n : ℕ) (hn : 0 < n) :
    splitRadicalH1Representation linePlusSplittingS (linePlusRep n) ≅ modularBinaryRep (n + 1) 0 :=
  Rep.mkIso (Representation.Equiv.mk (lowerRadicalH1Coordinate n hn) (by
    intro m
    apply LinearMap.ext
    intro cohomology
    change groupCohomology.H1 (lowerRadicalLatticeRep n) at cohomology
    change lowerRadicalH1Coordinate n hn
        (splitRadicalH1Action linePlusSplittingS (linePlusRep n) m cohomology) =
      Binary.homogeneousAction (n + 1) 0
        (GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL m))
        (lowerRadicalH1Coordinate n hn cohomology)
    rw [lineS_H1_action]
    exact lowerRadicalH1Coordinate_equivariant hn _ cohomology))

/-- `H¹` of the radical cohomology of `Λ₁⁺` is `H¹(SL(2, ℤ), Sym^{n+1})`. -/
def linePlusLeviCohomologyIso (n : ℕ) (hn : 0 < n) :
    groupCohomology.H1 (splitRadicalH1Representation linePlusSplittingS (linePlusRep n)) ≅
      groupCohomology.H1 (modularBinaryRep (n + 1) 0) :=
  (groupCohomology.functor ℂ (SpecialLinearGroup (Fin 2) ℤ) 1).mapIso (linePlusRadicalCoordinateIso n hn)

/-- Restriction of a relative two-cocycle of `Λ₁` to `Λ₁⁺`. -/
def linePlusRestrictS (n : ℕ) :
    relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep n) →ₗ[ℂ]
      relativeTwoCocycles linePlusExtensionS.inl (linePlusRep n) where
  toFun c := ⟨twoCocycleRestriction Lam1Plus.subtype (goodLineCoefficientRep n) c.val,
    fun a b => c.property a b⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lineS_splitEdgeCycle (n : ℕ) (m : SpecialLinearGroup (Fin 2) ℤ)
    (c : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep n)) :
    splitEdgeCycle linePlusSplittingS (linePlusRep n) m (linePlusRestrictS n c) =
      splitEdgeCycle goodLineSplitting (goodLineCoefficientRep n) (SpecialLinearGroup.toGL m) c := by
  apply groupCohomology.cocycles₁_ext
  intro r
  change c.val.val (goodLineLeviSection (SpecialLinearGroup.toGL m),
      goodLineRadicalInclusion (splitRadicalInput linePlusSplittingS m r)) -
      c.val.val (goodLineRadicalInclusion r, goodLineLeviSection (SpecialLinearGroup.toGL m)) =
    c.val.val (goodLineLeviSection (SpecialLinearGroup.toGL m),
      goodLineRadicalInclusion (splitRadicalInput goodLineSplitting
        (SpecialLinearGroup.toGL m) r)) -
      c.val.val (goodLineRadicalInclusion r, goodLineLeviSection (SpecialLinearGroup.toGL m))
  rw [lineS_radicalInput]

private theorem lineEdge_coord_eq (n : ℕ) (hn : 0 < n) (m : SpecialLinearGroup (Fin 2) ℤ)
    (c : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep n)) :
    lowerRadicalH1Coordinate n hn (groupCohomology.H1π _
        (splitEdgeCycle linePlusSplittingS (linePlusRep n) m (linePlusRestrictS n c))) =
      lowerRadicalH1Coordinate n hn (groupCohomology.H1π _
        (splitEdgeCycle goodLineSplitting (goodLineCoefficientRep n)
          (SpecialLinearGroup.toGL m) c)) := by
  rw [lineS_splitEdgeCycle]

/-- The edge cocycles of `Λ₁⁺` and `Λ₁` agree after the binary coordinate isomorphisms. -/
theorem linePlusEdge_restrict_cocycle (n : ℕ) (hn : 0 < n)
    (c : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep n)) :
    (groupCohomology.map (MonoidHom.id _) (linePlusRadicalCoordinateIso n hn).hom 1)
        (groupCohomology.H1π _ (splitCocycleEdge linePlusSplittingS (linePlusRep n) (linePlusRestrictS n c))) =
      restriction (n + 1) 0 0
        ((groupCohomology.map (MonoidHom.id _) (goodLineRadicalCoordinateIso n hn).hom 1)
          (groupCohomology.H1π _ (splitCocycleEdge goodLineSplitting
            (goodLineCoefficientRep n) c))) := by
  rw [groupCohomology.H1π_comp_map_apply, groupCohomology.H1π_comp_map_apply, restriction_apply]
  refine congrArg (fun z => groupCohomology.H1π (modularBinaryRep (n + 1) 0) z) ?_
  apply groupCohomology.cocycles₁_ext
  intro m
  exact lineEdge_coord_eq n hn m c

/-- **Compatibility of the edges.** The `Λ₁⁺`-edge of the restriction of a relative `Λ₁`-cocycle, in binary coordinates, is the `SL(2, ℤ)`-restriction of the
library's good-line edge of its class. -/
theorem linePlusEdge_restrict (n : ℕ) (hn : 0 < n)
    (c : relativeTwoCocycles goodLineRadicalInclusion (goodLineCoefficientRep n)) :
    (linePlusLeviCohomologyIso n hn).hom (linePlusEdgeS n
        (relativeTwoCocycleClass linePlusExtensionS.inl (linePlusRep n) (linePlusRestrictS n c))) =
      restriction (n + 1) 0 0 (goodLineBinaryEdge n hn
        (relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep n) c)) :=
  (congrArg (fun x => (linePlusLeviCohomologyIso n hn).hom x)
      (splitCohomologyEdge_apply linePlusSplittingS (linePlusRep n) (linePlusRestrictS n c))).trans
    ((linePlusEdge_restrict_cocycle n hn c).trans
      (congrArg (fun x => restriction (n + 1) 0 0 x) (goodLineBinaryEdge_apply n hn c).symm))

end TernaryPeriodPolynomials.Argument.LineSeed
