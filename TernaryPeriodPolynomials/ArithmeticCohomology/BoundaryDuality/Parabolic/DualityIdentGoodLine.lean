module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentCochain
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIdentClass
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelOne
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Kostant.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.CuspDualL2
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineLocalOp
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.LocalUniqueness
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LAHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LALocalOp
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LineCycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.LineRestriction

@[expose] public section


/-!
# The Levi cocycle of the good line is minus the edge image of the fiber class

For a homogeneous two-cocycle `ζ` of the good-line stabilizer `Λ₁` (the value at the line `⟨e₃⟩` of
a class of the maximal stratum) with an equivariant primitive `ω_U` over the radical lattice, the
fiber integration produces the cocycle `bridgeX` of `GL₂(ℤ)`, `γ ↦ Φ(A(k_γ⁻¹))`.  The relative
representative of `ζ` (`ParabolicDualityIdentCochain`) has the edge cocycle

  `goodLineBinaryEdgeCycle = - bridgeX`       (trivial character, coefficients `Sym^{n+1}`),
  `goodLineBinaryEdgeCycleT = - bridgeX`      (odd character, coefficients `Sym^{n+1} ⊗ det⁻¹`)

*exactly*, as cocycles.  Hence the class of `bridgeX` in `H¹(GL₂(ℤ), -)` is minus the Hochschild–Serre
edge image of the Shapiro coordinate of `ζ`, transported to the reference good line:

* `projectH1_bridgeX_eq_neg_phiL`: `[bridgeX] = - phiL (cuspRes z)` for the trivial character;
* `projectH1_bridgeX_eq_neg_edgeH2LT`: `[bridgeX] = - edgeH2LT (psiLT (cuspRes z))` for an odd
  character;
* consequently `bridgeX` is a parabolic cocycle when the coordinate is a local joint eigenclass with
  a small `T₂`-eigenvalue (`bridgeX_mem_parabolicCocycles`, `bridgeX_odd_mem_parabolicCocycles`),
  and its class is nonzero when the coordinate at the good line is nonzero
  (`projectH1_bridgeX_ne_zero`, `projectH1_bridgeX_odd_ne_zero`).

The identification of the line `L₁` of the Kostant data with the reference good line is
`L₁_eq_goodLine`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
  (fixedPointCycle fixedPointH2 fixedPointH2_classOf stabilizerTransportH2_fixedPointH2)
open TernaryPeriodPolynomials.Spectral.LineCoordinates (Λ₁)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (levelStabilizer)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL1)
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices (L₁ g₂)
open TernaryPeriodPolynomials.BoundaryDuality.CuspDualL2 (g₂_inv_val)
open TernaryPeriodPolynomials.BoundaryDuality.FiberL1 (dualRep)
open TernaryPeriodPolynomials.BoundaryDuality.FiberFormula (FiberHyp)
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives (dualityData)
open TernaryPeriodPolynomials.BoundaryDuality.Kostant
  (bridgeX phiTwist_trivial phiTwist_odd)

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident

open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne

/-! ### The line of the Kostant data is the reference good line -/

/-- **The line `⟨e₃⟩` of the Kostant data is the reference good line.** -/
theorem L₁_eq_goodLine : (L₁ : Flags .line) = QuotientGroup.mk rationalGoodLine := by
  change (QuotientGroup.mk g₂ : Flags .line) = QuotientGroup.mk rationalGoodLine
  rw [QuotientGroup.eq]
  refine ⟨?_, ?_⟩ <;> rw [Units.val_mul, g₂_inv_val] <;>
    simp [rationalGoodLine, Matrix.mul_apply, Fin.sum_univ_three]

/-- The stabilizer of the line `⟨e₃⟩` in the level is the arithmetic stabilizer `Λ₁` of the
reference good line. -/
theorem levelStabilizer_L₁ : levelStabilizer L₁ = Λ₁ :=
  (congrArg (fun F : Flags .line => levelStabilizer F) L₁_eq_goodLine).trans rfl

/-! ### The fiber data at the good line -/

/-- The fiber hypotheses at the good line `L₁` for the coefficients of the character `χ`. -/
abbrev GoodLineFiber (n : ℕ) (χ : RankOneCharacter) (Λe : Subgroup RationalGL3)
    (ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n)
    (ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n) : Prop :=
  FiberHyp (rationalCoefficientComponent n χ) (dualRep (dualityData n χ)) (dualityData n χ).B
    (levelStabilizer L₁) Λe latL1.sub ζ η ω ωU θU

/-- The primitive `ω_U` is a primitive of the cocycle `C` when `ζ` is the underlying function. -/
theorem hd_of_fiber {n : ℕ} {χ : RankOneCharacter} {Λe : Subgroup RationalGL3}
    {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
    {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}
    (hF : GoodLineFiber n χ Λe ζ η ω ωU θU) (C : cocycles Λ₁ (rationalCoefficientComponent n χ))
    (hζ : ∀ x, ζ x = C.val.val x) :
    ∀ a b c, differentialOneRaw ωU ![a, b, c] = C.val.val ![a, b, c] :=
  fun a b c => (hF.omegaU_d a b c).trans (hζ _)

/-! ### The trivial character -/

section Trivial

variable {n : ℕ} {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- **The relative two-cocycle of the good line** attached to the fiber data, trivial character. -/
def relOfL (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (C : cocycles Λ₁ (rationalCoefficientComponent n trivialCharacter))
    (hζ : ∀ x, ζ x = C.val.val x) : Spectral.GoodLineCoordinate.RelL n :=
  relOf (rationalCoefficientComponent n trivialCharacter) ωU C (hd_of_fiber hF C hζ)
    hF.omegaU_eq

/-- The relative representative has the class of the ambient two-cocycle. -/
theorem relOfL_H2 (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (C : cocycles Λ₁ (rationalCoefficientComponent n trivialCharacter))
    (hζ : ∀ x, ζ x = C.val.val x) :
    groupCohomology.H2π (goodLineCoefficientRep n) (relOfL hF C hζ).val =
      groupCohomology.H2π (goodLineCoefficientRep n) (ambientCocycleToGroup Λ₁ (ρn n) C) :=
  relOf_H2 (rationalCoefficientComponent n trivialCharacter) ωU C (hd_of_fiber hF C hζ)
    hF.omegaU_eq

/-- The class of the cocycle `C` lies in the classes with vanishing radical restriction. -/
theorem zetaClass_mem_KL (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (C : cocycles Λ₁ (rationalCoefficientComponent n trivialCharacter))
    (hζ : ∀ x, ζ x = C.val.val x) :
    classOf Λ₁ (ρn n) C ∈ Spectral.GoodLineHecke.KL n := by
  show Spectral.GoodLineHecke.toH2L n (classOf Λ₁ (ρn n) C) ∈
    LinearMap.ker (twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRep n))
  rw [Spectral.GoodLineHecke.toH2L_classOf, ← relOfL_H2 hF C hζ]
  exact (relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep n)
    (relOfL hF C hζ)).2

/-- **The edge cocycle of the relative representative is minus the cocycle `bridgeX`**, as
one-cocycles of `GL₂(ℤ)` with values in `Sym^{n+1}`. -/
theorem goodLineBinaryEdgeCycle_eq_neg_bridgeX (hn : 0 < n)
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (C : cocycles Λ₁ (rationalCoefficientComponent n trivialCharacter))
    (hζ : ∀ x, ζ x = C.val.val x) :
    goodLineBinaryEdgeCycle n hn (relOfL hF C hζ) = -bridgeX hn 0 (phiTwist_trivial n) hF := by
  apply groupCohomology.cocycles₁_ext
  intro γ
  rw [goodLineBinaryEdgeCycle_apply]
  exact coordinate_edge_eq_neg n hn trivialCharacter C ωU (hd_of_fiber hF C hζ) hF.omegaU_eq γ
    (goodLineRadicalEdgeCycle n (relOfL hF C hζ) γ)
    (fun p => goodLineSplitEdgeCycle_apply n (relOfL hF C hζ) γ p)

/-- **The edge image of the class of `C` is minus the class of `bridgeX`.** -/
theorem edgeK_zeta_eq_neg (hn : 0 < n) (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (C : cocycles Λ₁ (rationalCoefficientComponent n trivialCharacter))
    (hζ : ∀ x, ζ x = C.val.val x) :
    Spectral.GoodLineHecke.edgeK n hn ⟨classOf Λ₁ (ρn n) C, zetaClass_mem_KL hF C hζ⟩ =
      -projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX hn 0 (phiTwist_trivial n) hF) := by
  have e : Spectral.GoodLineHecke.edgeK n hn
      ⟨classOf Λ₁ (ρn n) C, zetaClass_mem_KL hF C hζ⟩ =
      goodLineBinaryEdge n hn (relativeTwoCocycleClass goodLineRadicalInclusion
        (goodLineCoefficientRep n) (relOfL hF C hζ)) := by
    show goodLineBinaryEdge n hn
      ⟨Spectral.GoodLineHecke.toH2L n (classOf Λ₁ (ρn n) C),
        zetaClass_mem_KL hF C hζ⟩ = _
    exact congrArg (goodLineBinaryEdge n hn) (Subtype.ext
      ((Spectral.GoodLineHecke.toH2L_classOf n C).trans (relOfL_H2 hF C hζ).symm))
  rw [e, ← goodLineBinaryEdgeCycle_H1, goodLineBinaryEdgeCycle_eq_neg_bridgeX hn hF C hζ]
  exact map_neg (projectH1 (arithmeticBinaryRep (n + 1) 0)) _

/-- **Identification, trivial character.**  The class of `bridgeX` in `H¹(GL₂(ℤ), Sym^{n+1})` is
minus the edge image of the class of `C`. -/
theorem projectH1_bridgeX_eq_neg_edgeK (hn : 0 < n)
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU)
    (C : cocycles Λ₁ (rationalCoefficientComponent n trivialCharacter))
    (hζ : ∀ x, ζ x = C.val.val x) :
    projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX hn 0 (phiTwist_trivial n) hF) =
      -Spectral.GoodLineHecke.edgeK n hn
        ⟨classOf Λ₁ (ρn n) C, zetaClass_mem_KL hF C hζ⟩ := by
  rw [edgeK_zeta_eq_neg hn hF C hζ, neg_neg]

end Trivial

/-! ### An odd character -/

section Odd

variable {n : ℕ} {χ : RankOneCharacter} {Λe : Subgroup RationalGL3}
  {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- **The relative two-cocycle of the good line** attached to the fiber data, twisted coefficients. -/
def relOfT (hF : GoodLineFiber n χ Λe ζ η ω ωU θU)
    (C : cocycles Λ₁ (rationalCoefficientComponent n χ)) (hζ : ∀ x, ζ x = C.val.val x) :
    Twisted.RelLT n χ :=
  relOf (rationalCoefficientComponent n χ) ωU C (hd_of_fiber hF C hζ) hF.omegaU_eq

/-- The relative representative has the class of the ambient two-cocycle. -/
theorem relOfT_H2 (hF : GoodLineFiber n χ Λe ζ η ω ωU θU)
    (C : cocycles Λ₁ (rationalCoefficientComponent n χ)) (hζ : ∀ x, ζ x = C.val.val x) :
    groupCohomology.H2π (Twisted.goodLineCoefficientRepT n χ) (relOfT hF C hζ).val =
      groupCohomology.H2π (Twisted.goodLineCoefficientRepT n χ)
        (ambientCocycleToGroup Λ₁ (rationalCoefficientComponent n χ) C) :=
  relOf_H2 (rationalCoefficientComponent n χ) ωU C (hd_of_fiber hF C hζ) hF.omegaU_eq

/-- **The edge cocycle of the relative representative is minus the cocycle `bridgeX`**, as
one-cocycles of `GL₂(ℤ)` with values in `Sym^{n+1} ⊗ det⁻¹`. -/
theorem goodLineBinaryEdgeCycleT_eq_neg_bridgeX
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n)
    (hF : GoodLineFiber n χ Λe ζ η ω ωU θU)
    (C : cocycles Λ₁ (rationalCoefficientComponent n χ)) (hζ : ∀ x, ζ x = C.val.val x) :
    Twisted.goodLineBinaryEdgeCycleT n χ hχ hn (relOfT hF C hζ) =
      -bridgeX hn (-1) (phiTwist_odd hχ) hF := by
  apply groupCohomology.cocycles₁_ext
  intro γ
  rw [Twisted.goodLineBinaryEdgeCycle_applyT]
  exact coordinate_edge_eq_neg n hn χ C ωU (hd_of_fiber hF C hζ) hF.omegaU_eq γ
    (Twisted.goodLineRadicalEdgeCycleT n χ (relOfT hF C hζ) γ)
    (fun p => Twisted.goodLineSplitEdgeCycle_applyT n χ (relOfT hF C hζ) γ p)

/-- **Identification, odd character.**  The class of `bridgeX` in `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`
is minus the edge image of the class of `C`. -/
theorem projectH1_bridgeX_eq_neg_edgeH2LT
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n)
    (hF : GoodLineFiber n χ Λe ζ η ω ωU θU)
    (C : cocycles Λ₁ (rationalCoefficientComponent n χ)) (hζ : ∀ x, ζ x = C.val.val x) :
    projectH1 (arithmeticBinaryRep (n + 1) (-1)) (bridgeX hn (-1) (phiTwist_odd hχ) hF) =
      -Twisted.edgeH2LT n χ hχ hn (classOf Λ₁ (rationalCoefficientComponent n χ) C) := by
  have h1 : Twisted.toH2LT n χ (classOf Λ₁ (rationalCoefficientComponent n χ) C) =
      groupCohomology.H2π (Twisted.goodLineCoefficientRepT n χ) (relOfT hF C hζ).val :=
    (Twisted.toH2LT_classOf n χ C).trans (relOfT_H2 hF C hζ).symm
  have e : Twisted.edgeH2LT n χ hχ hn (classOf Λ₁ (rationalCoefficientComponent n χ) C) =
      projectH1 (arithmeticBinaryRep (n + 1) (-1))
        (Twisted.goodLineBinaryEdgeCycleT n χ hχ hn (relOfT hF C hζ)) := by
    show Twisted.goodLineFullBinaryEdgeT n χ hχ hn
      (Twisted.toH2LT n χ (classOf Λ₁ (rationalCoefficientComponent n χ) C)) = _
    rw [h1]
    exact Twisted.goodLineFullBinaryEdgeT_relative n χ hχ hn (relOfT hF C hζ)
  rw [e, goodLineBinaryEdgeCycleT_eq_neg_bridgeX hχ hn hF C hζ,
    map_neg (projectH1 (arithmeticBinaryRep (n + 1) (-1))), neg_neg]

end Odd

/-! ### From a class of the maximal stratum to the good-line cocycle -/

/-- **The cocycle of the good-line stabilizer** attached to a cocycle on the flags: its value at the
reference good line `mk rationalGoodLine`. -/
def cocycleAtGoodLine (n : ℕ) (χ : RankOneCharacter)
    (cc : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line)) :
    cocycles Λ₁ (rationalCoefficientComponent n χ) :=
  fixedPointCycle rationalLevel (rationalCoefficientComponent n χ)
    (QuotientGroup.mk rationalGoodLine : Flags .line) cc

/-- The values of `cocycleAtGoodLine`. -/
theorem cocycleAtGoodLine_val (n : ℕ) (χ : RankOneCharacter)
    (cc : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line))
    (x : Fin 3 → RationalGL3) :
    (cocycleAtGoodLine n χ cc).val.val x = cc.val.val x (QuotientGroup.mk rationalGoodLine) :=
  rfl

/-- The fiber cocycle `ζ`, given by the value of `cc` at the line `L₁`, is the underlying function
of `cocycleAtGoodLine`. -/
theorem zeta_eq_cocycleAtGoodLine (n : ℕ) (χ : RankOneCharacter)
    (cc : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line))
    {ζ : (Fin 3 → RationalGL3) → HomogeneousPoly n} (hζ : ∀ x, ζ x = cc.val.val x L₁) :
    ∀ x, ζ x = (cocycleAtGoodLine n χ cc).val.val x := fun x =>
  (hζ x).trans (congrArg (fun F : Flags .line => cc.val.val x F) L₁_eq_goodLine)

/-- **The transport to the reference good line, trivial character**: the class of the good-line
cocycle is the transport of the Shapiro coordinate at the reference cusp. -/
theorem classOf_cocycleAtGoodLine (n : ℕ)
    (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)) :
    classOf Λ₁ (ρn n) (cocycleAtGoodLine n trivialCharacter cc) =
      Spectral.GoodLineLocalOp.psiL n
        (Spectral.CuspReduction.cuspRes n trivialCharacter .line true
          (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
            cc)) :=
  (fixedPointH2_classOf rationalLevel (ρn n) (QuotientGroup.mk rationalGoodLine : Flags .line)
    cc).symm.trans
    (stabilizerTransportH2_fixedPointH2 rationalLevel (ρn n)
      Spectral.GoodLineLocalOp.gammaL (Spectral.CuspOrbits.cuspFlag .line true)
      (QuotientGroup.mk rationalGoodLine) Spectral.GoodLineLocalOp.gammaL_smul
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc)).symm

/-- **The transport to the reference good line, general character.** -/
theorem classOf_cocycleAtGoodLine_psiLT (n : ℕ) (χ : RankOneCharacter)
    (cc : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line)) :
    classOf Λ₁ (rationalCoefficientComponent n χ) (cocycleAtGoodLine n χ cc) =
      Twisted.psiLT n χ
        (Spectral.CuspReduction.cuspRes n χ .line true
          (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) cc)) :=
  (fixedPointH2_classOf rationalLevel (rationalCoefficientComponent n χ)
    (QuotientGroup.mk rationalGoodLine : Flags .line) cc).symm.trans
    (stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n χ)
      Spectral.GoodLineLocalOp.gammaL (Spectral.CuspOrbits.cuspFlag .line true)
      (QuotientGroup.mk rationalGoodLine) Spectral.GoodLineLocalOp.gammaL_smul
      (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line)
        cc)).symm

/-! ### Consequences, trivial character -/

section TrivialStratum

variable {n : ℕ} {Λe : Subgroup RationalGL3} {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- **The class of `bridgeX` is minus the good-line edge of the Shapiro coordinate.**  Here `cc` is a
cocycle of the maximal line stratum whose value at `L₁` is the fiber cocycle `ζ`, and the Shapiro
coordinate of its class at the reference cusp is a local joint generalized eigenclass for a pair
character `c` with `‖c(T₂) - 1‖ ≤ 3/4`. -/
theorem projectH1_bridgeX_eq_neg_phiL (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (Spectral.TpExistence.tp Spectral.LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line))
    (hy : Spectral.CuspReduction.cuspRes n trivialCharacter .line true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc) ∈
      Spectral.CuspReduction.localJoint n trivialCharacter c .line true)
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU) (hζ : ∀ x, ζ x = cc.val.val x L₁) :
    projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX hn 0 (phiTwist_trivial n) hF) =
      -Spectral.LocalUniqueness.phiL n hn
        ⟨Spectral.CuspReduction.cuspRes n trivialCharacter .line true
          (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc),
          Spectral.LocalUniqueness.localJoint_le_ML c hc hy⟩ := by
  have hζC := zeta_eq_cocycleAtGoodLine n trivialCharacter cc hζ
  have key := projectH1_bridgeX_eq_neg_edgeK hn hF (cocycleAtGoodLine n trivialCharacter cc) hζC
  have hmem : Spectral.GoodLineLocalOp.psiL n
        (Spectral.CuspReduction.cuspRes n trivialCharacter .line true
          (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc)) ∈
      Spectral.GoodLineHecke.KL n :=
    (Submodule.mem_comap (f := Spectral.GoodLineLocalOp.psiL n)
      (p := Spectral.GoodLineHecke.KL n)).mp
      (Spectral.LocalUniqueness.localJoint_le_ML c hc hy)
  have hsub : (⟨classOf Λ₁ (ρn n) (cocycleAtGoodLine n trivialCharacter cc),
      zetaClass_mem_KL hF (cocycleAtGoodLine n trivialCharacter cc) hζC⟩ :
        Spectral.GoodLineHecke.KL n) =
      ⟨Spectral.GoodLineLocalOp.psiL n
        (Spectral.CuspReduction.cuspRes n trivialCharacter .line true
          (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc)),
        hmem⟩ :=
    Subtype.ext (classOf_cocycleAtGoodLine n cc)
  have e : Spectral.GoodLineHecke.edgeK n hn
      ⟨classOf Λ₁ (ρn n) (cocycleAtGoodLine n trivialCharacter cc),
        zetaClass_mem_KL hF (cocycleAtGoodLine n trivialCharacter cc) hζC⟩ =
      Spectral.LocalUniqueness.phiL n hn
        ⟨Spectral.CuspReduction.cuspRes n trivialCharacter .line true
          (classOf rationalLevel
            (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc),
          Spectral.LocalUniqueness.localJoint_le_ML c hc hy⟩ :=
    congrArg (Spectral.GoodLineHecke.edgeK n hn) hsub
  rw [key, e]

/-- **`bridgeX` is a parabolic cocycle** when the Shapiro coordinate of `cc` is a local joint
generalized eigenclass at the good line with a small `T₂`-eigenvalue. -/
theorem bridgeX_mem_parabolicCocycles (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (Spectral.TpExistence.tp Spectral.LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line))
    (hy : Spectral.CuspReduction.cuspRes n trivialCharacter .line true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc) ∈
      Spectral.CuspReduction.localJoint n trivialCharacter c .line true)
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU) (hζ : ∀ x, ζ x = cc.val.val x L₁) :
    bridgeX hn 0 (phiTwist_trivial n) hF ∈ parabolicCocycles (arithmeticBinaryRep (n + 1) 0) :=
  mem_parabolicCocycles_of_eq_neg (arithmeticBinaryRep (n + 1) 0)
    (phiL_mem_parabolicH1 n hn c hc hy) (projectH1_bridgeX_eq_neg_phiL hn c hc cc hy hF hζ)

/-- **The class of `bridgeX` is nonzero** when the Shapiro coordinate of `cc` at the good line is a
nonzero local joint generalized eigenclass. -/
theorem projectH1_bridgeX_ne_zero (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (Spectral.TpExistence.tp Spectral.LocalUniqueness.two) - 1‖ ≤ 3 / 4)
    (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line))
    (hy : Spectral.CuspReduction.cuspRes n trivialCharacter .line true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc) ∈
      Spectral.CuspReduction.localJoint n trivialCharacter c .line true)
    (hne : Spectral.CuspReduction.cuspRes n trivialCharacter .line true
        (classOf rationalLevel
          (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) cc) ≠ 0)
    (hF : GoodLineFiber n trivialCharacter Λe ζ η ω ωU θU) (hζ : ∀ x, ζ x = cc.val.val x L₁) :
    projectH1 (arithmeticBinaryRep (n + 1) 0) (bridgeX hn 0 (phiTwist_trivial n) hF) ≠ 0 := by
  rw [projectH1_bridgeX_eq_neg_phiL hn c hc cc hy hF hζ]
  refine neg_ne_zero.mpr (fun h => hne ?_)
  have h0 := Spectral.LocalUniqueness.phiL_injective hn
    (h.trans (map_zero (Spectral.LocalUniqueness.phiL n hn)).symm)
  exact congrArg Subtype.val h0

end TrivialStratum

/-! ### Consequences, odd character -/

section OddStratum

variable {n : ℕ} {χ : RankOneCharacter} {Λe : Subgroup RationalGL3}
  {ζ η : (Fin 3 → RationalGL3) → HomogeneousPoly n}
  {ω ωU θU : (Fin 2 → RationalGL3) → HomogeneousPoly n}

/-- **The class of `bridgeX` is minus the twisted good-line edge of the transported Shapiro
coordinate.** -/
theorem projectH1_bridgeX_eq_neg_edgeH2LT_psiLT
    (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1) (hn : 0 < n)
    (cc : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line))
    (hF : GoodLineFiber n χ Λe ζ η ω ωU θU) (hζ : ∀ x, ζ x = cc.val.val x L₁) :
    projectH1 (arithmeticBinaryRep (n + 1) (-1)) (bridgeX hn (-1) (phiTwist_odd hχ) hF) =
      -Twisted.edgeH2LT n χ hχ hn
        (Twisted.psiLT n χ
          (Spectral.CuspReduction.cuspRes n χ .line true
            (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line)
              cc))) := by
  rw [projectH1_bridgeX_eq_neg_edgeH2LT hχ hn hF (cocycleAtGoodLine n χ cc)
    (zeta_eq_cocycleAtGoodLine n χ cc hζ), classOf_cocycleAtGoodLine_psiLT]

/-- **`bridgeX` is a parabolic cocycle for an odd character** when the Shapiro coordinate is a local
joint generalized eigenclass at the good line with `‖c(T₂) + 1‖ ≤ 3/4`. -/
theorem bridgeX_odd_mem_parabolicCocycles (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hn : 0 < n) (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (Spectral.TpExistence.tp Spectral.LocalUniqueness.two) + 1‖ ≤ 3 / 4)
    (cc : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line))
    (hy : Spectral.CuspReduction.cuspRes n χ .line true
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) cc) ∈
      Spectral.CuspReduction.localJoint n χ c .line true)
    (hF : GoodLineFiber n χ Λe ζ η ω ωU θU) (hζ : ∀ x, ζ x = cc.val.val x L₁) :
    bridgeX hn (-1) (phiTwist_odd hχ) hF ∈ parabolicCocycles (arithmeticBinaryRep (n + 1) (-1)) :=
  mem_parabolicCocycles_of_eq_neg (arithmeticBinaryRep (n + 1) (-1))
    (edgeH2LT_mem_parabolicH1 n χ hχ hn c hc hy)
    (projectH1_bridgeX_eq_neg_edgeH2LT_psiLT hχ hn cc hF hζ)

/-- **The class of `bridgeX` is nonzero for an odd character** when the Shapiro coordinate at the
good line is nonzero. -/
theorem projectH1_bridgeX_odd_ne_zero (hχ : χ.toMonoidHom (realAdeleUnit (-1)) = -1)
    (hn : 0 < n) (cc : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n χ) .line))
    (hne : Spectral.CuspReduction.cuspRes n χ .line true
        (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) cc) ≠ 0)
    (hF : GoodLineFiber n χ Λe ζ η ω ωU θU) (hζ : ∀ x, ζ x = cc.val.val x L₁) :
    projectH1 (arithmeticBinaryRep (n + 1) (-1)) (bridgeX hn (-1) (phiTwist_odd hχ) hF) ≠ 0 := by
  rw [projectH1_bridgeX_eq_neg_edgeH2LT_psiLT hχ hn cc hF hζ]
  refine neg_ne_zero.mpr (fun h => hne ?_)
  have h1 := Twisted.edgeH2LT_injective n χ hχ hn
    (h.trans (map_zero (Twisted.edgeH2LT n χ hχ hn)).symm)
  exact Twisted.psiLT_injective n χ (h1.trans (map_zero (Twisted.psiLT n χ)).symm)

end OddStratum

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.Ident

end
