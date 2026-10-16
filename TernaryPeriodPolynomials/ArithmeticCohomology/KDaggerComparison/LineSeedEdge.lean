module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.CuspResProj
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Class.LevelEichler
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Good.LineHecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.EichlerClassicalTw
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.LineSource

@[expose] public section


/-!
# CMP-8 (entry, line half), edge theory: the good-line coordinate of the entry section and its Hochschild-Serre edge

Formalized by Claude Sonnet 5.5.

Line analogue of `EntrySeed.badPlane_edge`.  The good-line stabilizer `Λ₁ = {Q(3b, m, 1)} = ℤ² ⋊ GL₂(ℤ)` already has a complete edge theory in the
library (`Spectral.GoodLineHecke.edgeK : KL n → H¹(GL₂(ℤ), Sym^{n+1})`, injective, with `KL n` the classes whose restriction to the
lower radical vanishes; `edge` of a relative cocycle: `SourceConstruction.LineCupData.lineCup_edge`; surjectivity for split extensions:
`GammaNFacesFull.splitCohomologyEdge_surjective`).  What was missing, and is proved here, is the edge of the *coordinate of the entry section*:

* `edgeK_of_represents`: a stabilizer cocycle representing the cup product of the potentials of a `LineCupData` is a mixed class and its edge is `c` times
  the Levi class (`c` the Kostant constant);
* `goodLineClass`: the entry section `a_li = [goodLineWeight · lineSource D (lineLevi I)]`;
* `goodLine_edge`: the good-line coordinate of `a_li` (the Shapiro coordinate at the reference good line, transported to `⟨e₃⟩` by any transporter
  `γ`) lies in `KL n` and has edge `-3(n+1) · [Sw ∘ ψ_f ∘ pivot]`, where `ψ_f = classicalArithmeticCocycle f (n+1) … 0 0` is the classical period
  cocycle (twist `0`, parity `0`) of the level-one form `f = classicalFormOfEichlerInput I` of the Eichler input and `Sw ∘ ψ ∘ pivot` is the
  pivot-swap transport `dlCocycleOf`;
* `goodLine_coordinate_eq_smul_of_edge`: since `edgeK` is injective, the coordinate is the unique class of `KL n` with this edge.

Not covered: a geometric (zig-zag / de Rham) line seed class for the line face, the analogue of
`SeedC3S4c.ClassIdentity.eq_seed_of_edge`; the classical line seed is known here through its integral cochain `cΣ` (`EntryDictionary`) and through
the edge above.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.GoodLineHecke
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers

open TernaryPeriodPolynomials.Spectral.CuspReduction
open TernaryPeriodPolynomials.Spectral.CuspOrbits
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction
open TernaryPeriodPolynomials.AnalyticClasses
open TernaryPeriodPolynomials.TwistedSource
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein
open TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

open TernaryPeriodPolynomials.Spectral.IdentityPlaneCoordinate (ρn)
open TernaryPeriodPolynomials.Spectral.LineCoordinates (Λ₁)

/-- **The good-line edge of a cocycle representing the cup product of potentials.**  Such a cocycle is a mixed class (its restriction to
the lower radical vanishes), and its Hochschild-Serre edge in `H¹(GL₂(ℤ), Sym^{n+1})` (twist `0`) is `c` times the class of the Levi
cocycle, `c` the Kostant constant. -/
theorem edgeK_of_represents {n : ℕ} (hn : 0 < n) (D : LineCupData n) {c : ℂ} (hK : LineKostantLaw n D.lam c)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m, lineCocyclePhi n φ m = D.a (goodLineLeviSection m).val - D.a 1)
    (Z : cocycles (flagArithmeticStabilizer .line (QuotientGroup.mk rationalGoodLine))
      (rationalCoefficientComponent n trivialCharacter)) (hZ : D.Represents Z) :
    ∃ h : classOf Λ₁ (ρn n) Z ∈ KL n,
      edgeK n hn ⟨classOf Λ₁ (ρn n) Z, h⟩ = c • groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ := by
  have hmem : classOf Λ₁ (ρn n) Z ∈ KL n := by
    show toH2L n (classOf Λ₁ (ρn n) Z) ∈
      LinearMap.ker (twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRep n))
    rw [toH2L_classOf]
    exact (relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep n) (D.lineCupRelative hZ)).2
  refine ⟨hmem, ?_⟩
  have e : (⟨toH2L n (classOf Λ₁ (ρn n) Z), hmem⟩ :
      LinearMap.ker (twoCohomologyRestriction goodLineRadicalInclusion (goodLineCoefficientRep n))) =
      relativeTwoCocycleClass goodLineRadicalInclusion (goodLineCoefficientRep n) (D.lineCupRelative hZ) :=
    Subtype.ext (toH2L_classOf n Z)
  change goodLineBinaryEdge n hn ⟨toH2L n (classOf Λ₁ (ρn n) Z), hmem⟩ = _
  rw [e]
  exact D.lineCup_edge hZ hn hK φ hφ

theorem transport_cuspRes_line {n : ℕ} (γ : rationalLevel)
    (hγ : γ.val • cuspFlag .line true = (QuotientGroup.mk rationalGoodLine : Flags .line))
    (a : StratumH2 n trivialCharacter .line) :
    stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) γ (cuspFlag .line true)
        (QuotientGroup.mk rationalGoodLine) hγ (cuspRes n trivialCharacter .line true a) =
      fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
        (QuotientGroup.mk rationalGoodLine : Flags .line) a :=
  stabilizerTransportH2_fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) γ
    (cuspFlag .line true) (QuotientGroup.mk rationalGoodLine) hγ a

theorem coord_line_eq {n : ℕ} (γ : rationalLevel)
    (hγ : γ.val • cuspFlag .line true = (QuotientGroup.mk rationalGoodLine : Flags .line))
    (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)) :
    stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) γ (cuspFlag .line true)
        (QuotientGroup.mk rationalGoodLine) hγ
        (cuspRes n trivialCharacter .line true
          (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z)) =
      classOf Λ₁ (ρn n) (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
        (QuotientGroup.mk rationalGoodLine : Flags .line) z) := by
  rw [transport_cuspRes_line]
  exact fixedPointH2_classOf rationalLevel (rationalCoefficientComponent n trivialCharacter)
    (QuotientGroup.mk rationalGoodLine : Flags .line) z

/-- **The good-line section of the entry** `a_li`: the class of `goodLineWeight · lineSource` of the Eichler line datum. -/
def goodLineClass {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) (I : EichlerInput D.cusp n) :
    boundarySummand D .line :=
  SourceQuotient.sourceToSummand D .line
    ⟨fun y g => goodLineWeight g • lineSource D (SphericalEntryData.lineLevi (D := D) I) y g,
      SphericalEntryData.goodLine_isSourceCocycle S I⟩

theorem goodLineClass_val {n : ℕ} {D : InducingData n} (S : SphericalEntryData D) (I : EichlerInput D.cusp n) :
    (goodLineClass S I).val = SourceSpace.sourceClass D .line
      ⟨fun y g => goodLineWeight g • lineSource D (SphericalEntryData.lineLevi (D := D) I) y g,
        SphericalEntryData.goodLine_isSourceCocycle S I⟩ := rfl

theorem represents_line {n : ℕ} (M : CohomologicalCuspData n) (I : EichlerInput M.cusp n)
    (hls0 : IsSourceCocycle M.inducingData .line (lineSource M.inducingData (SphericalEntryData.lineLevi (D := M.inducingData) I))) :
    (dlCupData (SphericalEntryData.lineLevi (D := M.inducingData) I)).Represents
      (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
        (QuotientGroup.mk rationalGoodLine : Flags .line)
        (SourceSpace.evaluatedSource M.inducingData .line
          ⟨lineSource M.inducingData (SphericalEntryData.lineLevi (D := M.inducingData) I), hls0⟩)) := fun g h =>
  (SourceSpace.evaluatedSource_realizes M.inducingData .line ⟨_, hls0⟩ ![1, g.val, g.val * h.val]
    rationalGoodLine).trans
    (dlCupData_source M.inducingData (SphericalEntryData.lineLevi (D := M.inducingData) I) rfl _)

theorem phi_line {n : ℕ} (hn : Odd n) (M : CohomologicalCuspData n) (I : EichlerInput M.cusp n) (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
    lineCocyclePhi n (dlCocycleOf n (eichlerClassicalCocycle I hn)) m =
      (dlCupData (SphericalEntryData.lineLevi (D := M.inducingData) I)).a (goodLineLeviSection m).val -
        (dlCupData (SphericalEntryData.lineLevi (D := M.inducingData) I)).a 1 := by
  have hψ : ∀ m : Matrix.GeneralLinearGroup (Fin 2) ℤ, ((eichlerClassicalCocycle I hn) m : Binary.HomogeneousPoly (n + 1)) =
      (SphericalEntryData.lineLevi (D := M.inducingData) I).α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1 := fun m =>
    (eichlerCocycleTw_integral_eq_classical I (continuousStages M.inducingData) hn m).symm
  rw [dlCupData_levi]
  exact congrArg (binarySwap n) ((hψ (dlIntPivot m)).trans
    (congrArg (fun A => (SphericalEntryData.lineLevi (D := M.inducingData) I).α A 1) (dlIntPivot_map m)))

/-- **The Hochschild-Serre edge of the good-line coordinate of the entry section `a_li`** (line analogue of `badPlane_edge`).
The coordinate of `a_li` at the good line `⟨e₃⟩` (the Shapiro coordinate at the reference good line, transported to `⟨e₃⟩` by any
transporter `γ`) is a mixed class (zero restriction to the lower radical), and its edge in `H¹(GL₂(ℤ), Sym^{n+1})` (twist `0`) is `-3(n+1)`
times the class of the pivot-swap transport of the classical period cocycle of the level-one form of the Eichler input. -/
theorem goodLine_edge {n : ℕ} (hn : Odd n) (M : CohomologicalCuspData n) (S : SphericalEntryData M.inducingData)
    (I : EichlerInput M.cusp n)
    (γ : rationalLevel) (hγ : γ.val • cuspFlag .line true = (QuotientGroup.mk rationalGoodLine : Flags .line)) :
    ∃ h : (stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) γ (cuspFlag .line true)
        (QuotientGroup.mk rationalGoodLine) hγ
        (cuspRes n trivialCharacter .line true (goodLineClass S I).val) : H2 Λ₁ (ρn n)) ∈ KL n,
      edgeK n hn.pos ⟨_, h⟩ = ((-3 : ℂ) * ((n + 1 : ℕ) : ℂ)) •
        groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) (dlCocycleOf n (eichlerClassicalCocycle I hn)) := by
  have hls0 : IsSourceCocycle M.inducingData .line (lineSource M.inducingData (SphericalEntryData.lineLevi (D := M.inducingData) I)) :=
    lineSource_isSourceCocycle M.inducingData _ S.hχ
  have hcoord : cuspRes n trivialCharacter .line true (goodLineClass S I).val =
      cuspRes n trivialCharacter .line true (SourceSpace.sourceClass M.inducingData .line
        ⟨lineSource M.inducingData (SphericalEntryData.lineLevi (D := M.inducingData) I), hls0⟩) :=
    cuspRes_line_true_goodLine M.inducingData _ hls0 (SphericalEntryData.goodLine_isSourceCocycle S I)
  have hval := coord_line_eq γ hγ (SourceSpace.evaluatedSource M.inducingData .line
    ⟨lineSource M.inducingData (SphericalEntryData.lineLevi (D := M.inducingData) I), hls0⟩)
  obtain ⟨hmem, hedge⟩ := edgeK_of_represents hn.pos (dlCupData (SphericalEntryData.lineLevi (D := M.inducingData) I))
    (dl_lineKostantLaw n) _ (phi_line hn M I) _ (represents_line M I hls0)
  have hval' : stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) γ
      (cuspFlag .line true) (QuotientGroup.mk rationalGoodLine) hγ
      (cuspRes n trivialCharacter .line true (goodLineClass S I).val) =
      classOf Λ₁ (ρn n) (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
        (QuotientGroup.mk rationalGoodLine : Flags .line)
        (SourceSpace.evaluatedSource M.inducingData .line
          ⟨lineSource M.inducingData (SphericalEntryData.lineLevi (D := M.inducingData) I), hls0⟩)) := by
    rw [hcoord]
    exact hval
  refine ⟨(congrArg (· ∈ KL n) hval').mpr hmem, ?_⟩
  have hsub : (⟨_, (congrArg (· ∈ KL n) hval').mpr hmem⟩ : KL n) = ⟨_, hmem⟩ := Subtype.ext hval'
  rw [hsub]
  exact hedge

/-- The cocycle `ψ_f` of `goodLine_edge` is the classical period cocycle of the level-one form `classicalFormOfEichlerInput I`
(parity `0`, twist `0`). -/
theorem eichlerClassicalCocycle_eq {n : ℕ} {σ : CuspidalRepresentation} (I : EichlerInput σ n) (hn : Odd n) :
    eichlerClassicalCocycle I hn =
      classicalArithmeticCocycle (classicalFormOfEichlerInput I) (n + 1) (classicalFormOfEichlerInput_weight_eq I)
        (even_succ_of_odd_tw hn) 0 0 sign_zero_zero_tw := rfl

/-- **The coordinate of `a_li` is determined by its edge**: any class of `KL n` with the edge `[Sw ∘ ψ_f ∘ pivot]` has `-3(n+1)` times
itself equal to the transported good-line coordinate. -/
theorem goodLine_coordinate_eq_smul_of_edge {n : ℕ} (hn : Odd n) (M : CohomologicalCuspData n) (S : SphericalEntryData M.inducingData)
    (I : EichlerInput M.cusp n)
    (γ : rationalLevel) (hγ : γ.val • cuspFlag .line true = (QuotientGroup.mk rationalGoodLine : Flags .line))
    (y : KL n)
    (hy : edgeK n hn.pos y = groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0)
      (dlCocycleOf n (eichlerClassicalCocycle I hn))) :
    ∃ h : (stabilizerTransportH2 rationalLevel (rationalCoefficientComponent n trivialCharacter) γ (cuspFlag .line true)
        (QuotientGroup.mk rationalGoodLine) hγ
        (cuspRes n trivialCharacter .line true (goodLineClass S I).val) : H2 Λ₁ (ρn n)) ∈ KL n,
      (⟨_, h⟩ : KL n) = ((-3 : ℂ) * ((n + 1 : ℕ) : ℂ)) • y := by
  obtain ⟨h, he⟩ := goodLine_edge hn M S I γ hγ
  refine ⟨h, edgeK_injective n hn.pos ?_⟩
  rw [he, map_smul, hy]

end TernaryPeriodPolynomials.Argument.KDaggerComparison
