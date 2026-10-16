module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Seed.Edge

@[expose] public section


/-!
# The antiholomorphic seed: relative cocycle, complexified class and edge (Lemma C.3, S4c)

The antiholomorphic seed `ω̄_h = conj ω_h` of a level-one cusp form `f` has the relative 2-cocycle
`seedConjRelCocycle f` (the coefficientwise conjugate of `seedRelCocycle f`), whose complexified de
Rham class is `complexify_cuspSeedConjClass`, and whose `(1,1)` edge in the binary coordinates of
`H¹(SL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)` is `(n+1)⁻¹` times the class of the cocycle
`m ↦ \overline{ε_m}` (`seedConjEdge`, `seedConjEdge_of`), `ε` the Eichler cocycle.

Paper: Lemma C.3 (`ar:lem:seed`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial UpperHalfPlane

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3
open CategoryTheory groupCohomology

theorem map_conj_ddiv (q : Poly) :
    MvPolynomial.map (starRingEnd ℂ) (ddiv q) = ddiv (MvPolynomial.map (starRingEnd ℂ) q) := by
  apply MvPolynomial.ext
  intro d
  simp [ddiv, MvPolynomial.coeff_divMonomial, MvPolynomial.coeff_map]

theorem map_conj_unitShift (i : Fin 2) (idx : Fin 3) :
    MvPolynomial.map (starRingEnd ℂ) (unitShift i idx) = unitShift i idx := by
  unfold unitShift
  by_cases h : idx = i.castSucc <;> simp [h]

theorem map_conj_bind_unitShift (i : Fin 2) (P : Poly) :
    MvPolynomial.map (starRingEnd ℂ) (bind₁ (unitShift i) P) =
      bind₁ (unitShift i) (MvPolynomial.map (starRingEnd ℂ) P) := by
  rw [MvPolynomial.map_bind₁]
  congr 2
  funext idx
  exact map_conj_unitShift i idx

section

variable {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))

/-- The zig-zag cochain of the antiholomorphic seed, on `Λ₀⁺`. -/
def seedConjChain (g k : Lam0Plus) : Coef n :=
  cuspSeedConjCochain plusPlaneData plus_hΛ (f := f) g k

/-- The antiholomorphic seed cochain with values in the carrier of `plusRep n`. -/
def seedConjChainR (g k : Lam0Plus) : plusRep n := seedConjChain f g k

theorem seedConjChain_eq (g k : Lam0Plus) :
    seedConjChain f g k = Coef.conjCoef (seedChain f g k) :=
  cuspSeedConjCochain_eq plusPlaneData plus_hΛ g k

/-- The antiholomorphic seed cochain as a complex 2-cocycle of `Λ₀⁺`. -/
def seedConjCocycle₂ : cocycles₂ (plusRep n) :=
  ⟨fun p => seedConjChainR f p.1 p.2, (mem_cocycles₂_iff _).2 (fun g h j => by
    have e := cuspSeedConjCochain_cocycle plusPlaneData plus_hΛ (f := f) g h j
    change seedConjChainR f (g * h) j + seedConjChainR f g h =
      (plusRep n).ρ g (seedConjChainR f h j) + seedConjChainR f g (h * j)
    have e2 : (plusRep n).ρ g (seedConjChainR f h j) =
        plusPlaneData.rhoR n g (seedConjChain f h j) :=
      plusRep_ρ n g _
    rw [e2]
    exact e)⟩

theorem seedConjChain_inl_inl (r r' : RadicalLattice) :
    seedConjChain f (plusInl r) (plusInl r') = 0 := by
  rw [seedConjChain_eq, seedChain_inl_inl]
  apply Coef.toPoly_injective
  simp

/-- The relative 2-cocycle of the antiholomorphic seed. -/
def seedConjRelCocycle : relativeTwoCocycles plusExtensionS.inl (plusRep n) :=
  ⟨seedConjCocycle₂ f, fun r r' => seedConjChain_inl_inl f r r'⟩

/-- The complexification of the de Rham class of the antiholomorphic seed is the class of
`seedConjRelCocycle`. -/
theorem complexify_cuspSeedConjClass :
    complexify n (cuspSeedConjClass plusPlaneData plus_hΛ (f := f)) =
      (relativeTwoCocycleClass plusExtensionS.inl (plusRep n) (seedConjRelCocycle f)).val := by
  change complexify n (H2π (Rep.of (plusPlaneData.rhoR n)) (ZigZag.cochainCocycle _ _)) =
    H2π (plusRep n) (seedConjCocycle₂ f)
  rw [complexify_H2π]
  rfl

/-- Complex conjugation of a binary form. -/
def conjB (E : Binary.HomogeneousPoly (n + 1)) : Binary.HomogeneousPoly (n + 1) :=
  ⟨MvPolynomial.map (starRingEnd ℂ) E.val,
    (mem_homogeneousSubmodule _ _).mpr ((mem_homogeneousSubmodule _ _ |>.mp E.property).map _)⟩

/-- The mixed radical cocycle of the antiholomorphic seed. -/
def edgeCycConj (m : SpecialLinearGroup (Fin 2) ℤ) :
    groupCohomology.cocycles₁ (upperRadicalLatticeRep n) :=
  splitEdgeCycle plusSplittingS (plusRep n) m (seedConjRelCocycle f)

/-- The mixed part of the antiholomorphic seed cocycle, with values in `E_n`. -/
def edgeValConj (m : SpecialLinearGroup (Fin 2) ℤ) (r : RadicalLattice) : Coef n :=
  splitEdgeCycle plusSplittingS (plusRep n) m (seedConjRelCocycle f) r

theorem edgeValConj_eq (m : SpecialLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    edgeValConj f m r = Coef.conjCoef (edgeVal f m r) := by
  change seedConjChain f (plusSectionS m) (plusInl (splitRadicalInput plusSplittingS m r)) -
      seedConjChain f (plusInl r) (plusSectionS m) =
    Coef.conjCoef (seedChain f (plusSectionS m) (plusInl (splitRadicalInput plusSplittingS m r)) -
      seedChain f (plusInl r) (plusSectionS m))
  rw [seedConjChain_eq, seedConjChain_eq]
  apply Coef.toPoly_injective
  simp

theorem lvec_edgeCycConj (m : SpecialLinearGroup (Fin 2) ℤ) (i : Fin 2) :
    lvec n (edgeCycConj f m (radicalLatticeGenerator i)) =
      -(C (((n : ℂ) + 1)⁻¹) * ddiv (bind₁ (unitShift i)
          (binaryPolynomialLift (conjB (epsB f m)).val) -
        binaryPolynomialLift (conjB (epsB f m)).val)) := by
  have h := toPoly_edgeCycle f m (radicalLatticeGenerator i)
  rw [gen_shift, ← unitShift_eq, seedEps_section] at h
  have h2 : lvec n (edgeCycConj f m (radicalLatticeGenerator i)) =
      MvPolynomial.map (starRingEnd ℂ) (Coef.toPoly (edgeVal f m (radicalLatticeGenerator i))) := by
    have := congrArg Coef.toPoly (edgeValConj_eq f m (radicalLatticeGenerator i))
    exact this
  rw [h2, h]
  simp only [map_neg, map_mul, MvPolynomial.map_C, map_sub, map_conj_ddiv, map_conj_bind_unitShift]
  have hc : (starRingEnd ℂ) (((n : ℂ) + 1)⁻¹) = ((n : ℂ) + 1)⁻¹ := by
    simp
  rw [hc]
  have hl : MvPolynomial.map (starRingEnd ℂ) (binaryPolynomialLift (epsB f m).val) =
      binaryPolynomialLift (conjB (epsB f m)).val := by
    simp [binaryPolynomialLift, conjB, MvPolynomial.map_rename]
  rw [hl]

theorem edge_coordinate_conj (m : SpecialLinearGroup (Fin 2) ℤ) :
    upperRadicalCocycleCoordinate n (edgeCycConj f m) =
      (((n : ℂ) + 1)⁻¹) • conjB (epsB f m) :=
  coordinate_of_gen n _ _ (lvec_edgeCycConj f m)

/-- **The binary cocycle of the antiholomorphic seed**: the image of the mixed radical class under
the library's coordinate isomorphism. -/
def conjEdgeCocycle (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ)) :
    groupCohomology.cocycles₁ (modularBinaryRep (n + 1) (-1)) :=
  groupCohomology.mapCocycles₁ (MonoidHom.id _) (plusRadicalCoordinateIso n).hom
    (splitCocycleEdge plusSplittingS (plusRep n) (seedConjRelCocycle f))

theorem conjEdgeCocycle_apply (m : SpecialLinearGroup (Fin 2) ℤ) :
    (conjEdgeCocycle f m : Binary.HomogeneousPoly (n + 1)) =
      (((n : ℂ) + 1)⁻¹) • conjB (epsB f m) := by
  have h : (conjEdgeCocycle f m : Binary.HomogeneousPoly (n + 1)) =
      upperRadicalCocycleCoordinate n (edgeCycConj f m) := by
    change upperRadicalH1Coordinate n (groupCohomology.H1π _
        (splitEdgeCycle plusSplittingS (plusRep n) m (seedConjRelCocycle f))) = _
    exact upperRadicalH1Coordinate_apply (edgeCycConj f m)
  rw [h, edge_coordinate_conj]

/-- **The edge of the antiholomorphic seed.** In the binary coordinates the `(1,1)` edge of the
relative cocycle of the antiholomorphic seed of `f` is the class of `conjEdgeCocycle`, whose values
are `(n+1)⁻¹ \overline{ε_m}` (coefficientwise conjugate of the Eichler cocycle). -/
theorem seedConjEdge :
    (plusLeviCohomologyIso n).hom (plusEdgeS n
        (relativeTwoCocycleClass plusExtensionS.inl (plusRep n) (seedConjRelCocycle f))) =
      groupCohomology.H1π (modularBinaryRep (n + 1) (-1)) (conjEdgeCocycle f) := by
  have h1 : plusEdgeS n (relativeTwoCocycleClass plusExtensionS.inl (plusRep n)
      (seedConjRelCocycle f)) = groupCohomology.H1π (splitRadicalH1Representation plusSplittingS
        (plusRep n)) (splitCocycleEdge plusSplittingS (plusRep n) (seedConjRelCocycle f)) :=
    splitCohomologyEdge_apply plusSplittingS (plusRep n) (seedConjRelCocycle f)
  rw [h1]
  change (groupCohomology.map (MonoidHom.id _) (plusRadicalCoordinateIso n).hom 1)
    (groupCohomology.H1π _ (splitCocycleEdge plusSplittingS (plusRep n) (seedConjRelCocycle f))) = _
  rw [groupCohomology.H1π_comp_map_apply]
  rfl

/-- The `i`-normalized moment primitives are unique. -/
theorem momentPrim_unique (G : ℕ → ℂ → ℂ) (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (f (UpperHalfPlane.ofComplex z) * z ^ j) z)
    (j : ℕ) {w : ℂ} (hw : 0 < w.im) : G j w = momentPrim Lvl1 n f j w := by
  have hopen : IsOpen {u : ℂ | 0 < u.im} := isOpen_upperHalfPlaneSet
  have hconn : IsPreconnected {u : ℂ | 0 < u.im} :=
    (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  have heq : Set.EqOn (G j) (momentPrim Lvl1 n f j) {u : ℂ | 0 < u.im} := by
    refine hopen.eqOn_of_deriv_eq hconn
      (fun u hu => (hG j u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (momentPrim_hasDerivAt Lvl1 n f j u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => ?_) (show (0 : ℝ) < Complex.I.im by simp) ?_
    · rw [(hG j u hu).deriv, (momentPrim_hasDerivAt Lvl1 n f j u hu).deriv]
      rfl
    · rw [hG0 j, momentPrim_zero]
  exact heq hw

/-- The Eichler cocycle does not depend on the choice of normalized moment primitives. -/
theorem eichlerCocycle_eq_momentPrim (G : ℕ → ℂ → ℂ) (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (f (UpperHalfPlane.ofComplex z) * z ^ j) z)
    (m : SpecialLinearGroup (Fin 2) ℤ) :
    eichlerCocycle n G (SpecialLinearGroup.mapGL ℝ m) =
      eichlerCocycle n (momentPrim Lvl1 n f) (SpecialLinearGroup.mapGL ℝ m) := by
  have hpos : 0 < (SpecialLinearGroup.mapGL ℝ m : GL (Fin 2) ℝ).det.val := by
    simp [SpecialLinearGroup.mapGL]
  have hmob : mob (SpecialLinearGroup.mapGL ℝ m) Complex.I =
      ((SpecialLinearGroup.mapGL ℝ m • UpperHalfPlane.I : UpperHalfPlane) : ℂ) := by
    have := mob_eq_smul (SpecialLinearGroup.mapGL ℝ m) hpos UpperHalfPlane.I
    simpa using this
  have him : 0 < (mob (SpecialLinearGroup.mapGL ℝ m) Complex.I).im := by
    rw [hmob]; exact UpperHalfPlane.im_pos _
  unfold eichlerCocycle eichlerPoly
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [momentPrim_unique f G hG0 hG j him]

/-- **The edge of the antiholomorphic seed, against any cocycle with the conjugate Eichler
values.** If `c` is a cocycle of `modularBinaryRep (n+1) (-1)` with
`c(m) = \overline{ε_G(m)}` (coefficientwise conjugate of the Eichler cocycle of any normalized
moment primitives `G` of `f`), then the edge of the antiholomorphic seed of `f` is
`(n+1)⁻¹ [c]`. -/
theorem seedConjEdge_of (G : ℕ → ℂ → ℂ) (hG0 : ∀ j, G j Complex.I = 0)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (G j) (f (UpperHalfPlane.ofComplex z) * z ^ j) z)
    (c : groupCohomology.cocycles₁ (modularBinaryRep (n + 1) (-1)))
    (hc : ∀ m, (c m : Binary.HomogeneousPoly (n + 1)).val =
      MvPolynomial.map (starRingEnd ℂ) (eichlerCocycle n G (SpecialLinearGroup.mapGL ℝ m))) :
    (plusLeviCohomologyIso n).hom (plusEdgeS n
        (relativeTwoCocycleClass plusExtensionS.inl (plusRep n) (seedConjRelCocycle f))) =
      (((n : ℂ) + 1)⁻¹) • groupCohomology.H1π (modularBinaryRep (n + 1) (-1)) c := by
  rw [seedConjEdge, ← map_smul]
  refine congrArg (fun z => groupCohomology.H1π (modularBinaryRep (n + 1) (-1)) z) ?_
  apply groupCohomology.cocycles₁_ext
  intro m
  rw [conjEdgeCocycle_apply]
  change _ = (((n : ℂ) + 1)⁻¹) • (c m : Binary.HomogeneousPoly (n + 1))
  congr 1
  apply Subtype.ext
  rw [hc m, eichlerCocycle_eq_momentPrim f G hG0 hG m]
  rfl

end

end TernaryPeriodPolynomials.Argument.SeedC3S4c
