module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.RadicalLaw
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceIdentity
public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Plane.SourceAlgebra

@[expose] public section


/-!
# The potentials of the plane source at the identity plane

For a Levi cocycle datum `E` the plane source at the identity adele and rational vertices is the cup
product of the two potentials `a x = α(A(x_∞)) 1` and `l x = R(b(x_∞))`
(`planeSource_rational_identity`).  These potentials form a `PlaneCupData`
(`sourceCupData`): the Levi potential does not see the radical lattice (`alpha_iwA_radical`:
the Iwasawa Levi block of a unipotent is orthogonal), and the radical potential satisfies the
cocycle law along the radical lattice (`planeRadical_radical`, from `planeRadical_iwP_mul`).  Its
radical cocycle on the lattice is `planeRadical` at the real unipotent, so the Kostant law holds
with `c = -1` (`kostantLaw_of_planeRadical`), and the Levi side is `a (s m) - a 1 = α(m) 1`
(`sourceA_levi`).

The headline `planeSource_cuspRes_identity_ne_zero` is the identity-plane cusp coordinate of the
plane source: it is nonzero as soon as the one-cocycle `m ↦ α(m) 1` of `GL₂(ℤ)` has nonzero class
in `H¹(GL₂(ℤ), arithmeticBinaryRep (n + 1) (-1))`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Spectral.CuspReduction (cuspRes)
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (RadicalLattice identityPlaneRadicalInclusion identityPlaneLeviSection arithmeticBinaryRep)

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

/-- The real image of a rational matrix. -/
local notation "ratReal" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

variable {n : ℕ}

/-- The real unipotent of a lattice point of the radical lattice. -/
def radicalUnipotent (r : RadicalLattice) : planeParabolic ℝ :=
  ⟨planeUnipotent (((r.toAdd.1 : ℤ) : ℝ)) (((r.toAdd.2 : ℤ) : ℝ)), planeUnipotent_mem _ _⟩

/-- The real Levi element of an integral matrix, in the plane parabolic. -/
def leviParabolic (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) : planeParabolic ℝ :=
  ⟨planeLevi (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1, planeLevi_mem _ _⟩

theorem ratReal_radical (r : RadicalLattice) :
    ratReal (identityPlaneRadicalInclusion r).val = (radicalUnipotent r).1 := by
  change Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (planeUnipotent ((r.toAdd.1 : ℤ) : ℚ) ((r.toAdd.2 : ℤ) : ℚ)) =
      planeUnipotent (((r.toAdd.1 : ℤ) : ℝ)) (((r.toAdd.2 : ℤ) : ℝ))
  rw [TernaryPeriodPolynomials.SphericalDetection.Helpers.map_planeUnipotent, map_intCast,
    map_intCast]

theorem ratReal_levi (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
    ratReal (identityPlaneLeviSection m).val = (leviParabolic m).1 := by
  change Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (planeLevi m 1)) =
      planeLevi (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLevi, planeBlock, Matrix.GeneralLinearGroup.map_apply]

theorem ratReal_one : ratReal (1 : RationalGL3) = 1 := map_one _

theorem alpha_one {σ : CuspidalRepresentation} (E : LeviCocycleData σ n) (x : BinaryAdelicGL) :
    E.α 1 x = 0 :=
  E.orth 1 (by simp) x

theorem iwA_one : iwA (1 : RealGL3) = 1 := by
  have h : iwP (1 : RealGL3) = 1 := Subtype.ext iwasawaB_one
  unfold iwA
  rw [h]
  exact leviBlockHom.map_one

theorem alpha_iwA_one {σ : CuspidalRepresentation} (E : LeviCocycleData σ n) :
    E.α (iwA (1 : RealGL3)) = fun _ => 0 :=
  funext fun x => by rw [iwA_one]; exact alpha_one E x

/-- **The Levi potential does not see the radical lattice**: the Iwasawa Levi block of a unipotent
is orthogonal, so the Levi cocycle vanishes on it. -/
theorem alpha_iwA_radical {σ : CuspidalRepresentation} (E : LeviCocycleData σ n)
    (r : RadicalLattice) :
    E.α (iwA (ratReal (identityPlaneRadicalInclusion r).val)) 1 = 0 := by
  rw [ratReal_radical]
  have h := alpha_iwA_mul E (radicalUnipotent r) 1 1
  rw [mul_one] at h
  have hl : leviBlock (radicalUnipotent r) = 1 := leviBlock_planeUnipotent _ _
  rw [h, hl, alpha_iwA_one E, alpha_one E]
  simp [binaryCohomologicalAction]

/-- The Levi potential at a Levi element of the section is the Levi cocycle at the identity
adele. -/
theorem alpha_iwA_levi {σ : CuspidalRepresentation} (E : LeviCocycleData σ n)
    (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
    E.α (iwA (leviParabolic m).1) 1 =
      E.α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1 := by
  have h := alpha_iwA_mul E (leviParabolic m) 1 1
  rw [mul_one] at h
  have hl : leviBlock (leviParabolic m) = Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) m :=
    leviBlock_planeLevi _ _
  rw [h, hl, alpha_iwA_one E]
  simp [binaryCohomologicalAction]

theorem leviStar_radical_inv (r : RadicalLattice) (Q : Binary.HomogeneousPoly (n + 1)) :
    leviStar trivialCharacter (n + 1) (radicalUnipotent r)⁻¹ Q = Q := by
  have hc : componentCharacter trivialCharacter (radicalUnipotent r).1 = 1 :=
    componentCharacter_planeUnipotent _ _ _
  have hl : leviBlock (radicalUnipotent r) = 1 := leviBlock_planeUnipotent _ _
  have h1 : leviStar trivialCharacter (n + 1) (radicalUnipotent r) Q = Q := by
    show componentCharacter trivialCharacter (radicalUnipotent r).1 •
      Binary.homogeneousAction (n + 1) (-1)
        (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) (leviBlock (radicalUnipotent r))) Q = Q
    simp [hc, hl]
  have h2 := leviStar_mul_apply trivialCharacter (n + 1) (radicalUnipotent r)⁻¹
    (radicalUnipotent r) Q
  rw [_root_.inv_mul_cancel, leviStar_one_apply, h1] at h2
  exact h2.symm

theorem planeVRep_radical (r : RadicalLattice) (w : PlaneV n) :
    planeVRep n (identityPlaneRadicalInclusion r) w =
      realCoefficientComponent n trivialCharacter (radicalUnipotent r).1 w := by
  change realCoefficientComponent n trivialCharacter
    (ratReal (identityPlaneRadicalInclusion r).val) w = _
  rw [ratReal_radical]

/-- **The cocycle law of the radical potential along the radical lattice.** -/
theorem planeRadical_radical (r : RadicalLattice) (g : PlaneStab) :
    planeRadical n trivialCharacter
        (iwP (ratReal ((identityPlaneRadicalInclusion r).val * g.val))) =
      planeRadical n trivialCharacter (radicalUnipotent r) +
        Representation.linHom (planeQRep n) (planeVRep n) (identityPlaneRadicalInclusion r)
          (planeRadical n trivialCharacter (iwP (ratReal g.val))) := by
  apply LinearMap.ext
  intro Q
  rw [LinearMap.add_apply, linHom_radical_apply, planeVRep_radical]
  have hp : ratReal ((identityPlaneRadicalInclusion r).val * g.val) =
      (radicalUnipotent r).1 * ratReal g.val := by
    rw [map_mul, ratReal_radical]
  rw [hp, planeRadical_iwP_mul trivialCharacter (radicalUnipotent r) (ratReal g.val) Q,
    leviStar_radical_inv]

/-- **The potentials of the plane source at the identity plane.** -/
def sourceCupData {σ : CuspidalRepresentation} (E : LeviCocycleData σ n) : PlaneCupData n where
  a x := E.α (iwA (ratReal x)) 1
  l x := planeRadical n trivialCharacter (iwP (ratReal x))
  lam r := planeRadical n trivialCharacter (radicalUnipotent r)
  a_radical r := by
    show E.α (iwA (ratReal (identityPlaneRadicalInclusion r).val)) 1 =
      E.α (iwA (ratReal (1 : RationalGL3))) 1
    rw [alpha_iwA_radical E r, ratReal_one, iwA_one, alpha_one E]
  l_radical r g := planeRadical_radical r g

theorem sourceA_levi {σ : CuspidalRepresentation} (E : LeviCocycleData σ n)
    (m : Matrix.GeneralLinearGroup (Fin 2) ℤ) :
    (sourceCupData E).a (identityPlaneLeviSection m).val - (sourceCupData E).a 1 =
      E.α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1 := by
  show E.α (iwA (ratReal (identityPlaneLeviSection m).val)) 1 -
    E.α (iwA (ratReal (1 : RationalGL3))) 1 = _
  rw [ratReal_levi, ratReal_one, iwA_one, alpha_one E, sub_zero, alpha_iwA_levi E]

/-- The plane source at the identity adele and rational vertices is the cup product of the
potentials. -/
theorem sourceCupData_identity (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hchi : D.chi = trivialCharacter) (x : Fin 3 → RationalGL3) :
    planeSource D E (fun i => ratReal (x i)) (rationalGroup (1 : RationalGL3)⁻¹) =
      ((sourceCupData E).l (x 2) - (sourceCupData E).l (x 1))
        ((sourceCupData E).a (x 1) - (sourceCupData E).a (x 0)) := by
  have hχ : ∀ u : IntegralAdelesˣ, D.chi.toMonoidHom (integralAdeleUnit u) = 1 := by
    intro u
    rw [hchi]
    rfl
  rw [planeSource_rational_identity D E hχ x, hchi]
  rfl

/-- **The identity-plane cusp coordinate of the plane source is nonzero**, provided the one-cocycle
`m ↦ α(m) 1` of `GL₂(ℤ)` (the Eichler cocycle at the identity adele) has nonzero class in
`H¹(GL₂(ℤ), arithmeticBinaryRep (n + 1) (-1))`. -/
theorem planeSource_cuspRes_identity_ne_zero (D : InducingData n) (E : LeviCocycleData D.cusp n)
    (hchi : D.chi = trivialCharacter) (pos : 0 < n) (odd : Odd n)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) (-1)))
    (hφ : ∀ m, cocyclePhi n φ m = E.α (Matrix.GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) (-1)) φ ≠ 0)
    {z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)}
    (hz : Evaluates D .plane (planeSource D E) z) :
    cuspRes n D.chi .plane false
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) z) ≠ 0 :=
  cuspRes_plane_false_ne_zero_of_evaluates D hchi (sourceCupData E)
    (kostantLaw_of_planeRadical (lam := (sourceCupData E).lam) (fun _ _ => rfl))
    (neg_ne_zero.mpr one_ne_zero) φ (fun m => (hφ m).trans (sourceA_levi E m).symm) hφ0 pos odd hz
    (sourceCupData_identity D E hchi)

end TernaryPeriodPolynomials.SourceConstruction
