module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.GoodPlaneCup
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.GoodPlaneLevi
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.RadicalLaw
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceLaws

@[expose] public section


/-!
# The potentials of the plane source at the good plane

For the good-plane flag `F = rational goodPlaneFrame` (`e₂ ↔ e₃`) and the rational frame
`gF = F · diag(1, 3, 1)` of the block coordinates of `ΛG`, the plane source at the adelic point
`goodPlanePoint = rationalGroup F⁻¹ · atInfinity gF` (real part `1`, finite part `F⁻¹`, integral) is
the cup product of the potentials

* `a y = N • E.α (iwA y) (atInfinity δ)`, `N = |det δ|^{(n+3)/2}`, `δ = diag(1, 3)`;
* `l y = planeRadical (iwP y)`

(`gpCup`).  Indeed `goodPlanePoint = planeLevi (atInfinity δ) 1 · (atFinite F⁻¹)`, and the Levi law of
the plane source (`planeSourceAt_levi`) moves the real Levi `δ` into the argument of the cuspidal
function, while the integral finite part disappears (`planeSourceAt_integral`).  The radical
potential is the radical cocycle of the real plane parabolic on the standard radical lattice, so the
Kostant law holds with `c = -1` (`gpCup_kostant`).  Over the translated vertices `gF · y` the source
at `rationalGroup F⁻¹` is the `gF`-translate of the cup chain of `gpCup`
(`planeSource_goodPlane_translate`).

Original work by Claude Opus 5.5 (AxiomCode).
-/

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.LevelThree.GoodPlaneFrame
open TernaryPeriodPolynomials.LevelThree.GoodPlaneModel (goodPlaneExtension uq_one)
open TernaryPeriodPolynomials.LevelThree.GoodPlaneEdge2 (Phi)
open TernaryPeriodPolynomials.Spectral.CuspOrbits (goodPlaneFrame)
open TernaryPeriodPolynomials.Spectral.PlaneCoordinates (P_val)
open TernaryPeriodPolynomials.Spectral.IdentityPlaneCosets (icast)
open TernaryPeriodPolynomials.Spectral.LevelOneCosets (integralEmbed_val)
open TernaryPeriodPolynomials.BoundaryFiniteness.IntegralFlags (rational)

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The real image of a rational matrix. -/
local notation "ratReal" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

/-! ## Two adelic matrices with the same real and finite parts are equal -/

theorem adelic_eq_of_parts {g g' : AdelicGL} (hr : realGroup g = realGroup g')
    (hf : finiteGroup g = finiteGroup g') : g = g' := by
  calc g = atInfinity (realPart g) * atFinite (finitePart g) := adelic_split g
    _ = atInfinity (realPart g') * atFinite (finitePart g') := by
      rw [show realPart g = realPart g' from hr, show finitePart g = finitePart g' from hf]
    _ = g' := (adelic_split g').symm

theorem gp_planeLevi_one {R : Type*} [CommRing R] :
    planeLevi (1 : GeneralLinearGroup (Fin 2) R) 1 = 1 :=
  (planeLeviHom R).map_one

/-! ## The finite part of the good-plane point and the translated frame -/

/-- **The real frame matrix.** `F⁻¹ gF = diag(1, 3, 1)`, the real Levi of `δ = diag(1, 3)`. -/
theorem gp_frame_mul :
    ratReal (((rational goodPlaneFrame)⁻¹ : RationalGL3) * gF) = planeLevi gpDelta 1 := by
  rw [rational_goodPlaneFrame_inv]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [GeneralLinearGroup.map_apply, Units.val_mul, rational_goodPlaneFrame_val, gF_val,
      planeLevi, planeBlock, gpDelta, del_val, Matrix.mul_apply, Fin.sum_univ_three]

/-- The finite part of the good-plane flag representative is an integral matrix. -/
theorem gp_finite_integral :
    ∃ k : GeneralLinearGroup (Fin 3) IntegralAdeles,
      finiteGroup (rationalGroup ((rational goodPlaneFrame)⁻¹ : RationalGL3)) =
        GeneralLinearGroup.map integralEmbedding k := by
  refine ⟨GeneralLinearGroup.map (Int.castRingHom IntegralAdeles) goodPlaneFrame, ?_⟩
  rw [rational_goodPlaneFrame_inv]
  apply Units.ext
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [finiteGroup_rational, rationalFinite, rational, goodPlaneFrame,
      GeneralLinearGroup.map_apply]

/-- **The good-plane point**: real part `F⁻¹ · gF = diag(1, 3, 1)`, finite part `F⁻¹`. -/
def goodPlanePoint : AdelicGL :=
  rationalGroup ((rational goodPlaneFrame)⁻¹ : RationalGL3) * atInfinity (ratReal gF)

/-- The finite part of the good-plane point, as an adele with trivial real part. -/
def goodPlaneBase : AdelicGL :=
  atFinite (finiteGroup (rationalGroup ((rational goodPlaneFrame)⁻¹ : RationalGL3)))

theorem gp_realGroup_point : realGroup goodPlanePoint = planeLevi gpDelta 1 := by
  unfold goodPlanePoint
  rw [realGroup_mul_atInfinity, realGroup_rational, ← map_mul]
  exact gp_frame_mul

theorem gp_finiteGroup_point :
    finiteGroup goodPlanePoint =
      finiteGroup (rationalGroup ((rational goodPlaneFrame)⁻¹ : RationalGL3)) := by
  unfold goodPlanePoint
  exact finiteGroup_mul_atInfinity _ _

theorem gp_realGroup_base : realGroup goodPlaneBase = 1 := by
  unfold goodPlaneBase
  exact realPart_atFinite _

theorem gp_finiteGroup_base :
    finiteGroup goodPlaneBase =
      finiteGroup (rationalGroup ((rational goodPlaneFrame)⁻¹ : RationalGL3)) := by
  unfold goodPlaneBase
  exact finitePart_atFinite _

/-- **The good-plane point is the real Levi `δ` times its integral finite part.** -/
theorem gp_point_eq : goodPlanePoint = planeLevi (atInfinity gpDelta) 1 * goodPlaneBase := by
  apply adelic_eq_of_parts
  · rw [gp_realGroup_point, map_mul, realGroup_planeLevi, realPart_atInfinity, realUnitPart_one',
      gp_realGroup_base, mul_one]
  · rw [gp_finiteGroup_point, map_mul, finiteGroup_planeLevi, finitePart_atInfinity,
      finiteUnitPart_one', gp_finiteGroup_base, gp_planeLevi_one, one_mul]

/-! ## The plane source at an adele with integral finite part -/

section Integral

variable {n : ℕ}

/-- The finite twist is trivial at an integral finite adele. -/
theorem twist_integral (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (k : GeneralLinearGroup (Fin 3) IntegralAdeles) (h : BinaryRealGL) (x : BinaryAdelicGL) :
    cFin D (GeneralLinearGroup.map integralEmbedding k) •
        E.α h (x * bFin (GeneralLinearGroup.map integralEmbedding k)) = E.α h x := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro ν
  simp only [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
  have hfpv : finitePlaneVector D.cusp D.chi 0 (((n : ℂ) + 3) / 2)
      (GeneralLinearGroup.map integralEmbedding k) (E.lift ν h).val = (E.lift ν h).val :=
    finitePlaneVector_integral D.chi 0 (((n : ℂ) + 3) / 2) hχ (E.spherical ν h) k
  rw [twist_coeff D E (GeneralLinearGroup.map integralEmbedding k) h x ν, hfpv, rz_lift]

/-- **The plane source at an adele with integral finite part.** -/
theorem planeSourceAt_integral (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (g : AdelicGL) (k : GeneralLinearGroup (Fin 3) IntegralAdeles)
    (hk : finiteGroup g = GeneralLinearGroup.map integralEmbedding k)
    (y : Fin 3 → RealGL3) (x : BinaryAdelicGL) :
    planeSourceAt D E y g x =
      realCoefficientComponent n D.chi (realGroup g)⁻¹
        ((planeRadical n D.chi (iwP (realGroup g * y 2)) -
            planeRadical n D.chi (iwP (realGroup g * y 1)))
          (E.α (iwA (realGroup g * y 1)) x - E.α (iwA (realGroup g * y 0)) x)) := by
  unfold planeSourceAt cF bF
  rw [hk, smul_sub, twist_integral D E hχ k, twist_integral D E hχ k]

/-- **The plane source at the good-plane point**, before taking the cup form. -/
theorem planeSourceAt_goodPlanePoint (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1)
    (Y : Fin 3 → RealGL3) :
    planeSourceAt D E Y goodPlanePoint 1 =
      gpN n • ((planeRadical n D.chi (iwP (Y 2)) - planeRadical n D.chi (iwP (Y 1)))
        (E.α (iwA (Y 1)) (atInfinity gpDelta) - E.α (iwA (Y 0)) (atInfinity gpDelta))) := by
  obtain ⟨k, hk⟩ := gp_finite_integral
  rw [gp_point_eq, planeSourceAt_levi D E hχ (atInfinity gpDelta) goodPlaneBase Y 1,
    planeSourceAt_integral D E hχ goodPlaneBase k (gp_finiteGroup_base.trans hk) Y
      (1 * atInfinity gpDelta),
    gp_realGroup_base]
  simp only [one_mul, _root_.inv_one, map_one, Module.End.one_apply]

end Integral

/-! ## The potentials -/

section Potentials

variable {n : ℕ}

theorem gp_ratReal_radInc (r : RadicalLattice) :
    ratReal (goodPlaneExtension.inl r).val = (radicalUnipotent r).1 := by
  change Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (planeUnipotent ((r.toAdd.1 : ℤ) : ℚ) ((r.toAdd.2 : ℤ) : ℚ)) =
      planeUnipotent (((r.toAdd.1 : ℤ) : ℝ)) (((r.toAdd.2 : ℤ) : ℝ))
  rw [TernaryPeriodPolynomials.SphericalDetection.Helpers.map_planeUnipotent, map_intCast,
    map_intCast]

/-- The real image of the Levi section `m ↦ Pg 0 m 1` is the real Levi of `κ(m)`. -/
theorem gp_ratReal_Pg (m : binaryArithmeticLevel) :
    ratReal (Pg 0 m 1) = planeLevi (gpKappa m) 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Pg, P_val, uq_one, icast, integralEmbed_val, planeLevi, planeBlock, gpKappa,
      GeneralLinearGroup.map_apply]

/-- **The potentials of the plane source at the good-plane point.** -/
def gpCup {σ : CuspidalRepresentation} (E : LeviCocycleData σ n) : GoodPlaneCupData n where
  a y := gpN n • E.α (iwA (ratReal y)) (atInfinity gpDelta)
  l y := planeRadical n trivialCharacter (iwP (ratReal y))
  lam r := planeRadical n trivialCharacter (radicalUnipotent r)
  a_radical r := by
    show gpN n • E.α (iwA (ratReal (goodPlaneExtension.inl r).val)) (atInfinity gpDelta) =
      gpN n • E.α (iwA (ratReal (1 : RationalGL3))) (atInfinity gpDelta)
    rw [gp_ratReal_radInc r, gp_alpha_radical E r, ratReal_one, iwA_one, alpha_one E]
  l_radical r g Q := by
    have hp : ratReal ((goodPlaneExtension.inl r).val * g) =
        (radicalUnipotent r).1 * ratReal g := by
      rw [map_mul, gp_ratReal_radInc r]
    show planeRadical n trivialCharacter (iwP (ratReal ((goodPlaneExtension.inl r).val * g))) Q =
      planeRadical n trivialCharacter (radicalUnipotent r) Q +
        realCoefficientComponent n trivialCharacter (ratReal (goodPlaneExtension.inl r).val)
          (planeRadical n trivialCharacter (iwP (ratReal g)) Q)
    rw [hp, gp_ratReal_radInc r,
      planeRadical_iwP_mul trivialCharacter (radicalUnipotent r) (ratReal g) Q,
      leviStar_radical_inv]

/-- **The Kostant law for the potentials of the good plane**, with the constant `-1`. -/
theorem gpCup_kostant {σ : CuspidalRepresentation} (E : LeviCocycleData σ n) :
    KostantLaw n (gpCup E).lam (-1) :=
  kostantLaw_of_planeRadical (fun _ _ => rfl)

/-- **The Levi potential of the good plane**: `Φ (a (Pg 0 m 1) - a 1) = Φ (N • E.α κ(m) (atInfinity δ))`. -/
theorem gpCup_leviDelta {σ : CuspidalRepresentation} (E : LeviCocycleData σ n)
    (m : binaryArithmeticLevel) :
    (gpCup E).leviDelta m = Phi n (gpN n • E.α (gpKappa m) (atInfinity gpDelta)) := by
  have h1 : ratReal (Pg 0 m 1) = (gpLevi (gpKappa m)).1 := gp_ratReal_Pg m
  show Phi n (gpN n • E.α (iwA (ratReal (Pg 0 m 1))) (atInfinity gpDelta) -
    gpN n • E.α (iwA (ratReal (1 : RationalGL3))) (atInfinity gpDelta)) = _
  rw [h1, gp_alpha_levi E, ratReal_one, iwA_one, alpha_one E, smul_zero, sub_zero]

end Potentials

/-! ## The plane source at the good-plane point is the cup product of the potentials -/

section Source

variable {n : ℕ}

/-- **The plane source at the good-plane point and rational vertices.** -/
theorem planeSource_goodPlanePoint (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hchi : D.chi = trivialCharacter) (y : Fin 3 → RationalGL3) :
    planeSource D E (fun i => ratReal (y i)) goodPlanePoint =
      ((gpCup E).l (y 2) - (gpCup E).l (y 1)) ((gpCup E).a (y 1) - (gpCup E).a (y 0)) := by
  have hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1 := by
    intro u
    rw [hchi]
    rfl
  show planeSourceAt D E (fun i => ratReal (y i)) goodPlanePoint 1 = _
  rw [planeSourceAt_goodPlanePoint D E hχ, hchi]
  show gpN n • ((planeRadical n trivialCharacter (iwP (ratReal (y 2))) -
        planeRadical n trivialCharacter (iwP (ratReal (y 1))))
      (E.α (iwA (ratReal (y 1))) (atInfinity gpDelta) -
        E.α (iwA (ratReal (y 0))) (atInfinity gpDelta))) =
    (planeRadical n trivialCharacter (iwP (ratReal (y 2))) -
        planeRadical n trivialCharacter (iwP (ratReal (y 1))))
      (gpN n • E.α (iwA (ratReal (y 1))) (atInfinity gpDelta) -
        gpN n • E.α (iwA (ratReal (y 0))) (atInfinity gpDelta))
  exact ((map_smul (planeRadical n trivialCharacter (iwP (ratReal (y 2))) -
      planeRadical n trivialCharacter (iwP (ratReal (y 1)))) (gpN n)
      (E.α (iwA (ratReal (y 1))) (atInfinity gpDelta) -
        E.α (iwA (ratReal (y 0))) (atInfinity gpDelta))).symm).trans
    (congrArg (planeRadical n trivialCharacter (iwP (ratReal (y 2))) -
      planeRadical n trivialCharacter (iwP (ratReal (y 1))))
      (smul_sub (gpN n) (E.α (iwA (ratReal (y 1))) (atInfinity gpDelta))
        (E.α (iwA (ratReal (y 0))) (atInfinity gpDelta))))

/-- **The plane source at `rationalGroup F⁻¹` on the `gF`-translated rational vertices** is the
`gF`-translate of the cup chain of the potentials of `gpCup`. -/
theorem planeSource_goodPlane_translate (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hchi : D.chi = trivialCharacter) (y : Fin 3 → RationalGL3) :
    planeSource D E (fun i => ratReal (gF * y i))
        (rationalGroup ((rational goodPlaneFrame)⁻¹ : RationalGL3)) =
      rationalCoefficientComponent n D.chi gF
        (((gpCup E).l (y 2) - (gpCup E).l (y 1)) ((gpCup E).a (y 1) - (gpCup E).a (y 0))) := by
  have hy : (fun i => ratReal (gF * y i)) = fun i => ratReal gF * ratReal (y i) :=
    funext fun i => map_mul (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)) gF (y i)
  have e : planeSourceAt D E (fun i => ratReal gF * ratReal (y i))
      (rationalGroup ((rational goodPlaneFrame)⁻¹ : RationalGL3)) 1 =
      realCoefficientComponent n D.chi (ratReal gF)
        (planeSourceAt D E (fun i => ratReal (y i))
          (rationalGroup ((rational goodPlaneFrame)⁻¹ : RationalGL3) * atInfinity (ratReal gF)) 1) :=
    planeSourceAt_equivariant D E (ratReal gF) (fun i => ratReal (y i))
      (rationalGroup ((rational goodPlaneFrame)⁻¹ : RationalGL3)) 1
  show planeSourceAt D E (fun i => ratReal (gF * y i))
    (rationalGroup ((rational goodPlaneFrame)⁻¹ : RationalGL3)) 1 = _
  rw [hy, e]
  exact congrArg (realCoefficientComponent n D.chi (ratReal gF))
    (planeSource_goodPlanePoint D E hchi y)

end Source

end TernaryPeriodPolynomials.SourceConstruction
