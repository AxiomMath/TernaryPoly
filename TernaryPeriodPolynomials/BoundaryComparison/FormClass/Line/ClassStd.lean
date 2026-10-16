module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Line.Face
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Line.UnfoldLin
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.GramBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.PropC5GammaN

@[expose] public section


/-!
# U6 at the standard pair: the line restriction of the classical series is the averaged line-face class with explicit coefficients

Formalized by Claude Sonnet 5.5.
And `ar:eq:constantterms`.

For the holomorphic series `ℰ(f)` at the identity plane cusp and the standard line cusp `Q` (`h = 1`):
* `lineIso : Γ_P ≃ Γ_Q` (`g ↦ ȷ g`) and `lineIsoPull`: the pullback of classes of `Γ_Q = gammaNQAt N 1` to `Γ_P`;
* `lineIsoPull_rLine`: `lineIsoPull (rLine N n 1 c) = psiQ^* c` for every global class `c` of `Γ(N)`;
* `lineStd_series_class`: `lineIsoPull (rLine N n 1 [ℰ(f)]_ℂ)` is the (complexified) de Rham class of the radical average `avInvT (lineFaceForm ℰ(f))`;
* `lineStd_series_class_coeff`: and the coordinates of that average are the explicit coefficients `lineA1` (sum over free orbits of the `ℝ²`-integrals).
-/

open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.EisensteinDual
open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.Statements.EisensteinClass
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section
namespace TernaryPeriodPolynomials.Argument.FormClassK

variable (N : ℕ) [NeZero N] (n : ℕ)

omit [NeZero N] in
theorem jmath_mem_gammaNQAt_one {g : SL(3, ℤ)} (hg : g ∈ gammaNP N) : jmath g ∈ gammaNQAt N 1 := by
  have h1 : g ∈ gammaNPAt N 1 := by
    rw [mem_gammaNPAt, one_mul, inv_one, mul_one]; exact hg
  have := jmath_mem_gammaNQAt_iff.2 h1
  rwa [jmath_one] at this

/-- `ȷ : Γ_P → Γ_Q` for the standard line group `Γ_Q = gammaNQAt N 1`. -/
def lineIso : gammaNP N →* gammaNQAt N 1 where
  toFun g := ⟨jmath g.1, jmath_mem_gammaNQAt_one N g.2⟩
  map_one' := Subtype.ext jmath_one
  map_mul' g h := Subtype.ext (jmath_mul g.1 h.1)

/-- The complex coefficient representation of `Γ_P` through `ȷ`. -/
abbrev rhoQC : Representation ℂ (gammaNP N) (GeneralEisenstein.HomogeneousPoly n) :=
  (gammaRhoC (gammaN N) n).comp (psiQ N)

/-- The pullback of classes of the standard line group to `Γ_P` along `ȷ`. -/
def lineIsoPull : groupCohomology.H2 (lineFaceRep N 1 n) →ₗ[ℂ] groupCohomology.H2 (Rep.of (rhoQC N n)) :=
  (groupCohomology.map (lineIso N) (resMorK (lineIso N) (rhoQC N n) ((ambRep n).comp (gammaNQAt N 1).subtype)
    (fun _ => rfl)) 2).hom

omit [NeZero N] in
/-- The `ȷ`-pullback of the restriction to the standard line group is the pullback along `psiQ`. -/
theorem lineIsoPull_rLine (c : groupCohomology.H2 (gammaNRepAll N n)) :
    lineIsoPull N n (rLine N n 1 c) =
      (groupCohomology.map (psiQ N) (resMorK (psiQ N) (rhoQC N n) (gammaRhoC (gammaN N) n) (fun _ => rfl)) 2).hom c := by
  induction c using groupCohomology.H2_induction_on with
  | h z =>
    have e1 : rLine N n 1 (groupCohomology.H2π (gammaNRepAll N n) z) =
        groupCohomology.H2π (Rep.res (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N 1 hp)) (gammaNRepAll N n))
          (twoCocycleRestriction (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN N 1 hp)) (gammaNRepAll N n) z) :=
      twoCohomologyRestriction_apply _ _ z
    refine (congrArg (lineIsoPull N n) e1).trans ?_
    refine (groupCohomology.H2π_comp_map_apply _ _ _).trans ?_
    refine Eq.trans ?_ (groupCohomology.H2π_comp_map_apply _ _ _).symm
    refine congrArg (CategoryTheory.ConcreteCategory.hom (groupCohomology.H2π _)) ?_
    apply Subtype.ext
    funext p
    rfl

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham in
/-- **U6 at the standard pair.**  The `ȷ`-read restriction of the (complexified) class of the holomorphic series `ℰ(f)` to the standard line group `Γ_Q` is the (complexified) de Rham class
of the radical average of the line-face pullback of `ℰ(f)`. -/
theorem lineStd_series_class (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) :
    lineIsoPull N n (rLine N n 1 (Statements.EisensteinClass.eisensteinClassC_gammaN N n f hn)) =
      cxGen (rhoQ N n) (rhoQC N n) (fun _ _ => rfl)
        (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action (rhoQ N n)
          ((lineTwist N n).avInvT
            (lineFaceForm N n (planeEisensteinInv (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N))))) := by
  set F := planeEisensteinInv (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N) with hF
  set x : groupCohomology.H2 (Rep.of (gammaRho (gammaN N) n)) :=
    ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct (gammaN N)) (gammaRho (gammaN N) n) F with hx
  calc lineIsoPull N n (rLine N n 1 (Statements.EisensteinClass.eisensteinClassC_gammaN N n f hn))
      = lineIsoPull N n (rLine N n 1 (cxGen (gammaRho (gammaN N) n) (gammaRhoC (gammaN N) n) (fun _ _ => rfl) x)) :=
        congrArg (fun c => lineIsoPull N n (rLine N n 1 c)) (cxGen_eq_complexify (n := n) (Γ := gammaN N) x).symm
    _ = (groupCohomology.map (psiQ N) (resMorK (psiQ N) (rhoQC N n) (gammaRhoC (gammaN N) n) (fun _ => rfl)) 2).hom
          (cxGen (gammaRho (gammaN N) n) (gammaRhoC (gammaN N) n) (fun _ _ => rfl) x) :=
        lineIsoPull_rLine N n _
    _ = cxGen (rhoQ N n) (rhoQC N n) (fun _ _ => rfl)
          ((groupCohomology.map (psiQ N) (resMor (psiQ N) (rhoQ N n) (gammaRho (gammaN N) n) (fun _ => rfl)) 2).hom x) :=
        (cxGen_map (rhoQ N n) (rhoQC N n) (fun _ _ => rfl) (gammaRho (gammaN N) n)
          (gammaRhoC (gammaN N) n) (fun _ _ => rfl) (psiQ N) (fun _ => rfl) (fun _ => rfl) x).symm
    _ = _ := congrArg _ (lineFace_avg_class N n F).symm

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham in
/-- **U6 at the standard pair, with explicit coordinates.**  The class of `lineStd_series_class` is that of the closed form whose coordinates are S6's `lineA1`
(the sum over the free orbits of the `ℝ²`-integrals, `eq:intertwiner` unfolded). -/
theorem lineStd_series (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) :
    lineIsoPull N n (rLine N n 1 (Statements.EisensteinClass.eisensteinClassC_gammaN N n f hn)) =
      cxGen (rhoQ N n) (rhoQC N n) (fun _ _ => rfl)
        (ZigZag.deRhamClass isOpen_faceSet convex_faceSet faceSet_nonempty (gammaNPlaneData N).action (rhoQ N n)
          ((lineTwist N n).avInvT
            (lineFaceForm N n (planeEisensteinInv (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N))))) ∧
    ∀ {x : Face}, x ∈ faceSet → ∀ (p q : Fin 4) (m : Fin 3 →₀ ℕ),
      (Coef.toPoly (((((lineTwist N n).avInvT
        (lineFaceForm N n (planeEisensteinInv (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N))) :
          ZigZag.invClosed isOpen_faceSet (gammaNPlaneData N).action (rhoQ N n)) :
            Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2) x
          ![Pi.single p 1, Pi.single q 1])).coeff m = EisensteinClass.lineA1 N n f x p q m :=
  ⟨lineStd_series_class N n f hn, fun hx p q m => EisensteinClass.lineAvg_coeff_eq_lineA1 N n f hn hx p q m⟩

end TernaryPeriodPolynomials.Argument.FormClassK
