module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.EdgeCoord
public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.ConjRel
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Seed.EdgeConj

@[expose] public section


/-!
# The edges of the holomorphic and antiholomorphic line seeds (LS14e)

`lineEdgeCocycle f` is the binary cocycle of `H¹(SL₂(ℤ), Sym^{n+1})` (twist `0`) obtained from the mixed radical class of the relative seed cocycle of `Λ₁⁺`; its values are
`-3 · Sw(ε_{m'})` (`lineEdgeCocycle_apply`, `edge_coordinate_line`) and `lineSeedEdge` identifies the edge of the seed class with its class.  The same for the
antiholomorphic seed (`lineConjEdgeCocycle`, values `-3 · Sw(conj ε_{m'})`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein MvPolynomial Matrix CategoryTheory groupCohomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.AnalyticClasses (binarySwap)
open TernaryPeriodPolynomials.Argument.LineSeed
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c (Lvl1 conjB)

section

variable {n : ℕ} (hn : 0 < n) (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))

/-- **The binary cocycle of the line seed**: the image of the mixed radical class under the library's coordinate isomorphism. -/
def lineEdgeCocycle : cocycles₁ (modularBinaryRep (n + 1) 0) :=
  mapCocycles₁ (MonoidHom.id _) (linePlusRadicalCoordinateIso n hn).hom
    (splitCocycleEdge linePlusSplittingS (linePlusRep n) (lineSeedRelCocycle f))

theorem lineEdgeCocycle_apply (m : SpecialLinearGroup (Fin 2) ℤ) :
    (lineEdgeCocycle hn f m : Binary.HomogeneousPoly (n + 1)) = (-3 : ℂ) • binarySwap n (epsB f m) := by
  have h : (lineEdgeCocycle hn f m : Binary.HomogeneousPoly (n + 1)) =
      lowerRadicalCocycleCoordinate n (edgeCyc f m) := by
    change lowerRadicalH1Coordinate n hn (groupCohomology.H1π _
        (splitEdgeCycle linePlusSplittingS (linePlusRep n) m (lineSeedRelCocycle f))) = _
    exact lowerRadicalH1Coordinate_apply hn (edgeCyc f m)
  rw [h, edge_coordinate_line]

/-- **The edge of the line seed**, in the binary coordinates of `H¹(SL₂(ℤ), Sym^{n+1})`. -/
theorem lineSeedEdge :
    (linePlusLeviCohomologyIso n hn).hom (linePlusEdgeS n
        (relativeTwoCocycleClass linePlusExtensionS.inl (linePlusRep n) (lineSeedRelCocycle f))) =
      H1π (modularBinaryRep (n + 1) 0) (lineEdgeCocycle hn f) := by
  have h1 : linePlusEdgeS n (relativeTwoCocycleClass linePlusExtensionS.inl (linePlusRep n)
      (lineSeedRelCocycle f)) = H1π (splitRadicalH1Representation linePlusSplittingS
        (linePlusRep n)) (splitCocycleEdge linePlusSplittingS (linePlusRep n) (lineSeedRelCocycle f)) :=
    splitCohomologyEdge_apply linePlusSplittingS (linePlusRep n) (lineSeedRelCocycle f)
  rw [h1]
  change (groupCohomology.map (MonoidHom.id _) (linePlusRadicalCoordinateIso n hn).hom 1)
    (H1π _ (splitCocycleEdge linePlusSplittingS (linePlusRep n) (lineSeedRelCocycle f))) = _
  rw [groupCohomology.H1π_comp_map_apply]
  rfl

/-- The antiholomorphic seed cochain with values in `HomogeneousPoly n`. -/
def chainPConj (g k : Lam1Plus) : HomogeneousPoly n := lineSeedConjChain f g k

theorem toPoly_pivotT_conj (x : HomogeneousPoly n) :
    ((pivotT n (show HomogeneousPoly n from Coef.conjCoef (show Coef n from x)) : HomogeneousPoly n) :
        MvPolynomial (Fin 3) ℂ) =
      MvPolynomial.map (starRingEnd ℂ) ((pivotT n x : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) := by
  rw [toPoly_pivotT, toPoly_pivotT, map_neg, MvPolynomial.map_bind₁]
  have hx : ((show HomogeneousPoly n from Coef.conjCoef (show Coef n from x)) : MvPolynomial (Fin 3) ℂ) =
      MvPolynomial.map (starRingEnd ℂ) (x : MvPolynomial (Fin 3) ℂ) := rfl
  rw [hx]
  have : (fun i => MvPolynomial.map (starRingEnd ℂ) ((![X 2, X 1, X 0] : Fin 3 → MvPolynomial (Fin 3) ℂ) i)) =
      (![X 2, X 1, X 0] : Fin 3 → MvPolynomial (Fin 3) ℂ) := by
    funext i; fin_cases i <;> simp
  rw [this]

/-- The mixed radical cocycle of the antiholomorphic seed. -/
def edgeCycConj (m : SpecialLinearGroup (Fin 2) ℤ) : cocycles₁ (lowerRadicalLatticeRep n) :=
  splitEdgeCycle linePlusSplittingS (linePlusRep n) m (lineSeedConjRelCocycle f)

/-- The values of the mixed radical cocycle of the antiholomorphic seed. -/
def edgeValConj (m : SpecialLinearGroup (Fin 2) ℤ) (r : RadicalLattice) : HomogeneousPoly n := edgeCycConj f m r

theorem edgeValConj_eq_neg (m : SpecialLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    edgeValConj f m r = -(pivotT n (chainPConj f (linePlusInl r) (linePlusSectionS m))) := by
  change ((lineSeedConjRelCocycle f).val.val (linePlusSectionS m, linePlusInl (splitRadicalInput linePlusSplittingS m r)) -
      (lineSeedConjRelCocycle f).val.val (linePlusInl r, linePlusSectionS m) : linePlusRep n) = _
  have hA : (lineSeedConjRelCocycle f).val.val
      (linePlusSectionS m, linePlusInl (splitRadicalInput linePlusSplittingS m r)) = (0 : linePlusRep n) := by
    change pivotT n (lineSeedConjChain f (linePlusSectionS m) _) = 0
    rw [lineSeedConjChain_eq, lineSeedChain_section_left]
    have h0 : Coef.conjCoef (0 : Coef n) = 0 :=
      Coef.toPoly_injective (by rw [Coef.toPoly_conjCoef]; simp)
    rw [h0]
    exact map_zero _
  have hB : (lineSeedConjRelCocycle f).val.val (linePlusInl r, linePlusSectionS m) =
      pivotT n (chainPConj f (linePlusInl r) (linePlusSectionS m)) := rfl
  rw [hA, hB]
  exact zero_sub _

theorem edgeValConj_lift (m : SpecialLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    ((edgeValConj f m r : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) =
      binaryPolynomialLift (MvPolynomial.map (starRingEnd ℂ) (edgeBin f m r)) := by
  rw [edgeValConj_eq_neg, Submodule.coe_neg]
  have hc : chainPConj f (linePlusInl r) (linePlusSectionS m) =
      (show HomogeneousPoly n from Coef.conjCoef (show Coef n from chainP f (linePlusInl r) (linePlusSectionS m))) :=
    lineSeedConjChain_eq f _ _
  rw [hc, toPoly_pivotT_conj]
  have h2 := edgeCyc_eq_neg f m r
  have h3 : ((edgeVal f m r : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) =
      -((pivotT n (chainP f (linePlusInl r) (linePlusSectionS m)) : HomogeneousPoly n) : MvPolynomial (Fin 3) ℂ) := by
    rw [h2, Submodule.coe_neg]
  rw [edgeCyc_lift] at h3
  have h4 : ((pivotT n (chainP f (linePlusInl r) (linePlusSectionS m)) : HomogeneousPoly n) :
      MvPolynomial (Fin 3) ℂ) = -binaryPolynomialLift (edgeBin f m r) := by rw [h3, neg_neg]
  rw [h4, map_neg, neg_neg]
  simp [binaryPolynomialLift, MvPolynomial.map_rename]

/-- **The binary coordinate of the antiholomorphic seed**: `-3 · Sw(conj ε_{m'})`. -/
theorem edge_coordinate_line_conj (m : SpecialLinearGroup (Fin 2) ℤ) :
    lowerRadicalCocycleCoordinate n (edgeCycConj f m) = (-3 : ℂ) • binarySwap n (conjB (epsB f m)) := by
  apply Subtype.ext
  rw [coordinate_of_bin (edgeCycConj f m) _ _ (edgeValConj_lift f m radicalLatticeFirst)
    (edgeValConj_lift f m radicalLatticeSecond)]
  have h := congrArg (MvPolynomial.map (starRingEnd ℂ)) (contraction_edgeBin f m)
  simp only [map_sub, map_mul, MvPolynomial.map_X] at h
  rw [h]
  change MvPolynomial.map (starRingEnd ℂ) ((-3 : ℂ) • (binarySwap n (epsB f m)).val) =
    (-3 : ℂ) • (binarySwap n (conjB (epsB f m))).val
  simp only [smul_eq_C_mul, map_mul, MvPolynomial.map_C]
  congr 1
  · simp only [map_neg]
    exact congrArg (fun x => -MvPolynomial.C x) (map_ofNat (starRingEnd ℂ) 3)
  · change MvPolynomial.map (starRingEnd ℂ) (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (epsB f m).val) =
      MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) (MvPolynomial.map (starRingEnd ℂ) (epsB f m).val)
    exact (MvPolynomial.map_rename _ _ _)

/-- **The binary cocycle of the antiholomorphic line seed.** -/
def lineConjEdgeCocycle : cocycles₁ (modularBinaryRep (n + 1) 0) :=
  mapCocycles₁ (MonoidHom.id _) (linePlusRadicalCoordinateIso n hn).hom
    (splitCocycleEdge linePlusSplittingS (linePlusRep n) (lineSeedConjRelCocycle f))

theorem lineConjEdgeCocycle_apply (m : SpecialLinearGroup (Fin 2) ℤ) :
    (lineConjEdgeCocycle hn f m : Binary.HomogeneousPoly (n + 1)) =
      (-3 : ℂ) • binarySwap n (conjB (epsB f m)) := by
  have h : (lineConjEdgeCocycle hn f m : Binary.HomogeneousPoly (n + 1)) =
      lowerRadicalCocycleCoordinate n (edgeCycConj f m) := by
    change lowerRadicalH1Coordinate n hn (groupCohomology.H1π _
        (splitEdgeCycle linePlusSplittingS (linePlusRep n) m (lineSeedConjRelCocycle f))) = _
    exact lowerRadicalH1Coordinate_apply hn (edgeCycConj f m)
  rw [h, edge_coordinate_line_conj]

/-- **The edge of the antiholomorphic line seed.** -/
theorem lineConjSeedEdge :
    (linePlusLeviCohomologyIso n hn).hom (linePlusEdgeS n
        (relativeTwoCocycleClass linePlusExtensionS.inl (linePlusRep n) (lineSeedConjRelCocycle f))) =
      H1π (modularBinaryRep (n + 1) 0) (lineConjEdgeCocycle hn f) := by
  have h1 : linePlusEdgeS n (relativeTwoCocycleClass linePlusExtensionS.inl (linePlusRep n)
      (lineSeedConjRelCocycle f)) = H1π (splitRadicalH1Representation linePlusSplittingS
        (linePlusRep n)) (splitCocycleEdge linePlusSplittingS (linePlusRep n) (lineSeedConjRelCocycle f)) :=
    splitCohomologyEdge_apply linePlusSplittingS (linePlusRep n) (lineSeedConjRelCocycle f)
  rw [h1]
  change (groupCohomology.map (MonoidHom.id _) (linePlusRadicalCoordinateIso n hn).hom 1)
    (H1π _ (splitCocycleEdge linePlusSplittingS (linePlusRep n) (lineSeedConjRelCocycle f))) = _
  rw [groupCohomology.H1π_comp_map_apply]
  rfl

end

end TernaryPeriodPolynomials.Argument.LineSeed
