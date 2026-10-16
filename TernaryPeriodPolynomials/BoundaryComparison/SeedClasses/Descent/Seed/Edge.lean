module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Seed.Relative
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Seed.EdgeShear

@[expose] public section


/-!
# The edge of the seed cocycle in library coordinates (Lemma C.3, S4c)

For a level-one cusp form `f` of weight `n + 3`, the relative 2-cocycle `seedRelCocycle f` of
`Λ₀⁺ = ℤ² ⋊ SL₂(ℤ)` (`SeedRelative`) has the `(1,1)` Hochschild--Serre edge computed here, in the
binary coordinates `plusLeviCohomologyIso` of `H¹(SL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`:

`edge = (n+1)⁻¹ (-1)^{n+1} · [classicalBinaryCocycle f (n+1)]`   (`seedEdge`).

The computation: the mixed radical cocycle is `r ↦ -c(n_r, s(m))`
(`toPoly_edgeCycle`); on the lattice generators it is `-(n+1)⁻¹ ((S_{e_i} - 1) ε_m)/Z`, whose
infinitesimal pair (the inverse nilpotent average of the library's coordinates) is `(n+1)⁻¹ ∇ε_m`
(`avg_pair` of `SeedEdgeShear`, `pair_of_gen`); Euler's identity (`planeRadicalCoordinate_gradient`)
gives the coordinate `(n+1)⁻¹ ε_m` (`coordinate_of_gen`, `edge_coordinate`); and the Eichler
cocycle is `(-1)^{n+1}` times the library's holomorphic period cocycle (`epsB_eq`).

Paper: Lemma C.3 (`ar:lem:seed`).

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3
open CategoryTheory groupCohomology

theorem rho_par_one (w : Fin 2 → ℝ) (q : Poly) :
    rho (parabolicMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) w) q = bind₁ (shiftSub w) q := by
  rw [rho_eq_bind (1 : Matrix (Fin 2) (Fin 2) ℝ) w (by simp)]
  congr 2
  funext i
  have hinv := inv_parabolicMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) w (by simp)
  rw [hinv]
  fin_cases i <;> simp [shiftSub, Fin.sum_univ_three] <;> ring

theorem shiftSub_zero : shiftSub 0 = X := by
  funext i
  fin_cases i <;> simp [shiftSub]

theorem rho_par_zero (q : Poly) :
    rho (parabolicMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) 0) q = q := by
  rw [rho_par_one, shiftSub_zero, bind₁_X_left, AlgHom.id_apply]

section

variable {n : ℕ} (f : CuspForm Lvl1 ((n + 3 : ℕ) : ℤ))

theorem toPoly_seedChain_section (m : SpecialLinearGroup (Fin 2) ℤ) (k : Lam0Plus) :
    Coef.toPoly (seedChain f (plusSectionS m) k) = 0 := by
  rw [toPoly_seedChain]
  have hw : plusPlaneData.plm (plusSectionS m) =
      parabolicMatrix (plusPlaneData.lamM (plusSectionS m)) 0 := by
    rw [PlaneData.plm_eq]
    show parabolicMatrix _ (plusW (plusSectionS m)) = _
    rw [plusW_section]
  rw [hw, sub_self, ddiv_zero, mul_zero]

theorem toPoly_seedChain_inl (r : RadicalLattice) (k : Lam0Plus) :
    Coef.toPoly (seedChain f (plusInl r) k) = C (((n : ℂ) + 1)⁻¹) *
      ddiv (bind₁ (shiftSub ![(r.toAdd.1 : ℝ), (r.toAdd.2 : ℝ)]) (seedEps f k) - seedEps f k) := by
  rw [toPoly_seedChain]
  have hl : plusPlaneData.lamM (plusInl r) = 1 := by
    show ((plusLam (plusInl r) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = 1
    rw [plusLam_inl]
    rfl
  have hp : plusPlaneData.plm (plusInl r) =
      parabolicMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) ![(r.toAdd.1 : ℝ), (r.toAdd.2 : ℝ)] := by
    rw [PlaneData.plm_eq, hl]
    show parabolicMatrix 1 (plusW (plusInl r)) = _
    rw [plusW_inl]
  rw [hp, hl, rho_par_one, rho_par_zero]

/-- The mixed part of the seed cocycle, with values in `E_n`. -/
def edgeVal (m : SpecialLinearGroup (Fin 2) ℤ) (r : RadicalLattice) : Coef n :=
  splitEdgeCycle plusSplittingS (plusRep n) m (seedRelCocycle f) r

/-- The mixed part of the seed cocycle: `r ↦ -c(n_r, s(m))`. -/
theorem toPoly_edgeCycle (m : SpecialLinearGroup (Fin 2) ℤ) (r : RadicalLattice) :
    Coef.toPoly (edgeVal f m r) =
      -(C (((n : ℂ) + 1)⁻¹) *
        ddiv (bind₁ (shiftSub ![(r.toAdd.1 : ℝ), (r.toAdd.2 : ℝ)]) (seedEps f (plusSectionS m)) -
          seedEps f (plusSectionS m))) := by
  rw [← toPoly_seedChain_inl]
  change Coef.toPoly (seedChain f (plusSectionS m)
    (plusInl (splitRadicalInput plusSplittingS m r)) -
    seedChain f (plusInl r) (plusSectionS m)) = _
  rw [Coef.toPoly_sub, toPoly_seedChain_section, zero_sub]

/-- The Eichler cocycle of the seed's moment primitives, as a binary form of degree `n + 1`. -/
def epsB (m : SpecialLinearGroup (Fin 2) ℤ) : Binary.HomogeneousPoly (n + 1) :=
  ⟨eichlerCocycle n (momentPrim Lvl1 n f) (SpecialLinearGroup.mapGL ℝ m),
    (mem_homogeneousSubmodule _ _).mpr (eichlerCocycle_isHomogeneous n _ _)⟩

theorem seedEps_section (m : SpecialLinearGroup (Fin 2) ℤ) :
    seedEps f (plusSectionS m) = binaryPolynomialLift (epsB f m).val := by
  unfold seedEps
  rw [show plusPlaneData.lam (plusSectionS m) = SpecialLinearGroup.mapGL ℝ m from
    plusLam_section m]
  rfl

theorem gen_shift (i : Fin 2) :
    ![(((radicalLatticeGenerator i).toAdd.1 : ℤ) : ℝ),
      (((radicalLatticeGenerator i).toAdd.2 : ℤ) : ℝ)] = fun j => if j = i then (1 : ℝ) else 0 := by
  funext j
  fin_cases i <;> fin_cases j <;>
    simp [radicalLatticeGenerator, radicalLatticeFirst, radicalLatticeSecond]

/-- The mixed radical cocycle of the seed, as a cocycle of the library's upper radical
representation. -/
def edgeCyc (m : SpecialLinearGroup (Fin 2) ℤ) :
    groupCohomology.cocycles₁ (upperRadicalLatticeRep n) :=
  splitEdgeCycle plusSplittingS (plusRep n) m (seedRelCocycle f)

/-- The polynomial underlying a value of the upper radical representation. -/
def lvec (n : ℕ) (x : upperRadicalLatticeRep n) : Poly := (x : HomogeneousPoly n).1

/-- The averaging equivalence of the upper radical acts by the exponential average. -/
theorem upperRadicalAverageEquiv_apply (n : ℕ) (i : Fin 2) (x : HomogeneousPoly n) :
    upperRadicalAverageEquiv n i x =
      nilpotentExponentialAverage (upperRadicalGenerator n i) (n + 1) x :=
  (nilpotentAverageEquiv_apply _ _ _ _).trans
    (LinearMap.congr_fun (nilpotentExponentialAverage_inst_irrel _ _ _ _) x)

/-- **The infinitesimal pair from the generator values.** If the values of a radical-lattice
1-cocycle on the two generators are `-(n+1)⁻¹ ((S_{e_i} - 1) P)/Z` for the lift `P` of a binary form
`E`, its infinitesimal pair is `(n+1)⁻¹ ∇E`. -/
theorem pair_of_gen (n : ℕ) (c0 : groupCohomology.cocycles₁ (upperRadicalLatticeRep n))
    (E : Binary.HomogeneousPoly (n + 1))
    (h : ∀ i : Fin 2, lvec n (c0 (radicalLatticeGenerator i)) =
      -(C (((n : ℂ) + 1)⁻¹) * ddiv (bind₁ (unitShift i) (binaryPolynomialLift E.val) -
        binaryPolynomialLift E.val))) (i : Fin 2) :
    upperRadicalCocyclePair n c0 i = (((n : ℂ) + 1)⁻¹) • binaryGradientPair E i := by
  refine ((upperRadicalAverageEquiv n i).symm_apply_eq).mpr ?_
  rw [upperRadicalAverageEquiv_apply]
  symm
  have hP : (binaryPolynomialLift E.val).IsHomogeneous (n + 1) := by
    have := E.property.rename_isHomogeneous (f := Fin.castSucc)
    simpa [binaryPolynomialLift] using this
  refine (LinearMap.congr_fun (nilpotentExponentialAverage_inst_irrel _ _ _ _) _).trans
    (avg_pair n i _ hP _ _ ?_ (h i))
  rw [Submodule.coe_smul, smul_eq_C_mul]
  rfl

/-- **The binary coordinate from the generator values.** -/
theorem coordinate_of_gen (n : ℕ) (c0 : groupCohomology.cocycles₁ (upperRadicalLatticeRep n))
    (E : Binary.HomogeneousPoly (n + 1))
    (h : ∀ i : Fin 2, lvec n (c0 (radicalLatticeGenerator i)) =
      -(C (((n : ℂ) + 1)⁻¹) * ddiv (bind₁ (unitShift i) (binaryPolynomialLift E.val) -
        binaryPolynomialLift E.val))) :
    upperRadicalCocycleCoordinate n c0 = (((n : ℂ) + 1)⁻¹) • E := by
  change planeRadicalCoordinate n (upperRadicalCocyclePair n _) = _
  have h' : upperRadicalCocyclePair n c0 = (((n : ℂ) + 1)⁻¹) • binaryGradientPair E :=
    funext (pair_of_gen n c0 E h)
  rw [h', map_smul, planeRadicalCoordinate_gradient]

/-- **The binary coordinate of the mixed radical cocycle of the seed**: `(n+1)⁻¹ ε_m`. -/
theorem edge_coordinate (m : SpecialLinearGroup (Fin 2) ℤ) :
    upperRadicalCocycleCoordinate n (edgeCyc f m) = (((n : ℂ) + 1)⁻¹) • epsB f m := by
  refine coordinate_of_gen n _ _ fun i => ?_
  have h := toPoly_edgeCycle f m (radicalLatticeGenerator i)
  rw [gen_shift, ← unitShift_eq, seedEps_section] at h
  exact h

theorem epsB_eq (hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2)
    (m : SpecialLinearGroup (Fin 2) ℤ) :
    epsB f m = ((-1 : ℂ) ^ (n + 1)) • (show Binary.HomogeneousPoly (n + 1) from
      classicalBinaryCocycle f (n + 1) hw (-1) m) := by
  apply Subtype.ext
  have h := classicalBinaryCocycle_eq_eichlerCocycle f n hw (-1) (momentPrim Lvl1 n f)
    (momentPrim_zero Lvl1 n f) (momentPrim_hasDerivAt Lvl1 n f) m
  rw [Submodule.coe_smul, smul_eq_C_mul]
  change eichlerCocycle n (momentPrim Lvl1 n f) (SpecialLinearGroup.mapGL ℝ m) = _
  rw [h, ← mul_assoc, ← map_mul, ← mul_pow]
  norm_num

/-- **The edge of the seed.** The `(1,1)` Hochschild--Serre edge of the relative cocycle of the
seed of the level-one cusp form `f`, in the binary coordinates of `H¹(SL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`,
is `(n+1)⁻¹ (-1)^{n+1}` times the class of the library's holomorphic period cocycle
`classicalBinaryCocycle f (n+1)`. -/
theorem seedEdge (hw : ((n + 3 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) + 2) :
    (plusLeviCohomologyIso n).hom (plusEdgeS n
        (relativeTwoCocycleClass plusExtensionS.inl (plusRep n) (seedRelCocycle f))) =
      (((n : ℂ) + 1)⁻¹ * (-1 : ℂ) ^ (n + 1)) • groupCohomology.H1π (modularBinaryRep (n + 1) (-1))
        (classicalBinaryCocycle f (n + 1) hw (-1)) := by
  have h1 : plusEdgeS n (relativeTwoCocycleClass plusExtensionS.inl (plusRep n)
      (seedRelCocycle f)) = groupCohomology.H1π (splitRadicalH1Representation plusSplittingS
        (plusRep n)) (splitCocycleEdge plusSplittingS (plusRep n) (seedRelCocycle f)) :=
    splitCohomologyEdge_apply plusSplittingS (plusRep n) (seedRelCocycle f)
  rw [h1]
  change (groupCohomology.map (MonoidHom.id _) (plusRadicalCoordinateIso n).hom 1)
    (groupCohomology.H1π _ (splitCocycleEdge plusSplittingS (plusRep n) (seedRelCocycle f))) = _
  rw [groupCohomology.H1π_comp_map_apply, ← map_smul]
  refine congrArg (fun z => groupCohomology.H1π (modularBinaryRep (n + 1) (-1)) z) ?_
  apply groupCohomology.cocycles₁_ext
  intro m
  change upperRadicalH1Coordinate n (groupCohomology.H1π _
      (splitEdgeCycle plusSplittingS (plusRep n) m (seedRelCocycle f))) = _
  refine (upperRadicalH1Coordinate_apply (edgeCyc f m)).trans ?_
  rw [edge_coordinate, epsB_eq f hw m, smul_smul]
  rfl

end

end TernaryPeriodPolynomials.Argument.SeedC3S4c
