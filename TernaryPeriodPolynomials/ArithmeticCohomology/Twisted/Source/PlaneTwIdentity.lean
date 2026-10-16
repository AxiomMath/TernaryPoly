module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.PlaneTwSource
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.EichlerClassicalTw
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.DetectTwClass
public import TernaryPeriodPolynomials.ArithmeticCohomology.Twisted.Source.DetectTwRadical
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SourceCoordinate
public import TernaryPeriodPolynomials.ArithmeticCohomology.Separation.SphericalBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.Level.OneNontrivial
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelOneParity.Helpers

@[expose] public section


/-!
# Source construction at the identity plane for the odd character of conductor three

For the odd quadratic character `χ` of conductor three, the twisted plane source
`planeSourceTw D E` at the identity adele and rational vertices is the cup product of the two
potentials `a x = α(A(x_∞)) 1` and `l x = R(b(x_∞))` (`planeSourceTw_one`).  These potentials form a
`PlaneCupDataTw` (`sourceCupDataTw`): the Levi potential does not see the radical lattice
(`alpha_iwA_radical_tw`: the Iwasawa Levi block of a unipotent is orthogonal, and the sign-twisted
cocycle law of the Levi cocycle `alpha_iwA_mulTw` applies), and the radical potential satisfies the
cocycle law along the radical lattice (`planeRadical_radical_tw`, from `planeRadical_iwP_mul`; the
character `χ` is trivial on the unipotents).  Its radical cocycle on the lattice is `planeRadical`
at the real unipotent, so the Kostant law holds with `c = -1`, and the Levi side is
`a (s m) - a 1 = α(m) 1` (`sourceA_levi_tw`).

The headline `planeSourceTw_cuspRes_identity_ne_zero` is the identity-plane cusp coordinate of the
twisted plane source; it is nonzero as soon as the one-cocycle `m ↦ α(m) 1` of `GL₂(ℤ)` has nonzero
class in `H¹(GL₂(ℤ), arithmeticBinaryRep (n + 1) 0)`.  The final theorem
`sphericalSourceConstruction_of_conductorThree` supplies this class from the twisted Eichler
cocycle and concludes that some summand class has a nonzero identity-plane coordinate.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open Matrix GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SourceConstruction
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (identityPlaneRadicalInclusion identityPlaneLeviSection RadicalLattice arithmeticBinaryRep)
open TernaryPeriodPolynomials.AnalyticClasses (continuousStages)
open TernaryPeriodPolynomials.Spectral.LevelOneNontrivial
  (ConductorThree chi_realNegOne_eq_neg_one)
open TernaryPeriodPolynomials.Separation
  (SphericalSourceConstruction coordinateImage_ne_bot_iff)
open TernaryPeriodPolynomials.EisensteinGraph.StandardConstruction.SourceSpace
  (evaluatedSource evaluatedSource_realizes)

namespace TernaryPeriodPolynomials.TwistedSource

/-- The real image of a rational matrix. -/
local notation "ratReal" => Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ)

variable {n : ℕ}

/-! ## The real elements attached to the radical lattice and to integral Levi blocks -/

section RealElements

/-- The real unipotent of a lattice point of the radical lattice, in the real plane parabolic. -/
def radicalUnipotentTw (r : RadicalLattice) : planeParabolic ℝ :=
  ⟨planeUnipotent (((r.toAdd.1 : ℤ) : ℝ)) (((r.toAdd.2 : ℤ) : ℝ)), planeUnipotent_mem _ _⟩

/-- The real Levi element of an integral matrix, in the real plane parabolic. -/
def leviParabolicTw (m : GeneralLinearGroup (Fin 2) ℤ) : planeParabolic ℝ :=
  ⟨planeLevi (GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1, planeLevi_mem _ _⟩

theorem ratReal_radical_tw (r : RadicalLattice) :
    ratReal (identityPlaneRadicalInclusion r).val = (radicalUnipotentTw r).1 := by
  change GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (planeUnipotent ((r.toAdd.1 : ℤ) : ℚ) ((r.toAdd.2 : ℤ) : ℚ)) =
      planeUnipotent (((r.toAdd.1 : ℤ) : ℝ)) (((r.toAdd.2 : ℤ) : ℝ))
  rw [TernaryPeriodPolynomials.SphericalDetection.Helpers.map_planeUnipotent, map_intCast,
    map_intCast]

theorem ratReal_levi_tw (m : GeneralLinearGroup (Fin 2) ℤ) :
    ratReal (identityPlaneLeviSection m).val = (leviParabolicTw m).1 := by
  change GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (GeneralLinearGroup.map (Int.castRingHom ℚ) (planeLevi m 1)) =
      planeLevi (GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeLevi, planeBlock, GeneralLinearGroup.map_apply]

theorem ratReal_one_tw : ratReal (1 : RationalGL3) = 1 := map_one _

theorem iwA_one_tw : iwA (1 : RealGL3) = 1 := by
  have h : iwP (1 : RealGL3) = 1 := Subtype.ext iwasawaB_one
  unfold iwA
  rw [h]
  exact leviBlockHom.map_one

end RealElements

/-! ## The Levi potential -/

section LeviPotential

variable {σ : CuspidalRepresentation}

theorem alpha_one_tw (E : LeviCocycleDataTw σ n) (x : BinaryAdelicGL) : E.α 1 x = 0 :=
  E.orth 1 (by simp) x

theorem alpha_iwA_one_tw (E : LeviCocycleDataTw σ n) : E.α (iwA (1 : RealGL3)) = fun _ => 0 :=
  funext fun x => by rw [iwA_one_tw]; exact alpha_one_tw E x

/-- **The Levi potential does not see the radical lattice**: the Iwasawa Levi block of a unipotent
is orthogonal, so the sign-twisted Levi cocycle vanishes on it. -/
theorem alpha_iwA_radical_tw (E : LeviCocycleDataTw σ n) (r : RadicalLattice) :
    E.α (iwA (ratReal (identityPlaneRadicalInclusion r).val)) 1 = 0 := by
  rw [ratReal_radical_tw]
  have h := alpha_iwA_mulTw E (radicalUnipotentTw r) 1 1
  rw [mul_one] at h
  have hl : leviBlock (radicalUnipotentTw r) = 1 := leviBlock_planeUnipotent _ _
  rw [h, hl, alpha_iwA_one_tw E, alpha_one_tw E]
  simp [binaryCohomologicalAction]

/-- The Levi potential at a Levi element of the section is the Levi cocycle at the identity
adele. -/
theorem alpha_iwA_levi_tw (E : LeviCocycleDataTw σ n) (m : GeneralLinearGroup (Fin 2) ℤ) :
    E.α (iwA (leviParabolicTw m).1) 1 = E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1 := by
  have h := alpha_iwA_mulTw E (leviParabolicTw m) 1 1
  rw [mul_one] at h
  have hl : leviBlock (leviParabolicTw m) = GeneralLinearGroup.map (Int.castRingHom ℝ) m :=
    leviBlock_planeLevi _ _
  rw [h, hl, alpha_iwA_one_tw E]
  simp [binaryCohomologicalAction]

end LeviPotential

/-! ## The radical potential -/

section RadicalPotential

theorem leviStar_radical_inv_tw (χ : RankOneCharacter) (r : RadicalLattice)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    leviStar χ (n + 1) (radicalUnipotentTw r)⁻¹ Q = Q := by
  have hc : componentCharacter χ (radicalUnipotentTw r).1 = 1 :=
    componentCharacter_planeUnipotent _ _ _
  have hl : leviBlock (radicalUnipotentTw r) = 1 := leviBlock_planeUnipotent _ _
  have h1 : leviStar χ (n + 1) (radicalUnipotentTw r) Q = Q := by
    show componentCharacter χ (radicalUnipotentTw r).1 •
      Binary.homogeneousAction (n + 1) (-1)
        (GeneralLinearGroup.map (algebraMap ℝ ℂ) (leviBlock (radicalUnipotentTw r))) Q = Q
    simp [hc, hl]
  have h2 := leviStar_mul_apply χ (n + 1) (radicalUnipotentTw r)⁻¹ (radicalUnipotentTw r) Q
  rw [_root_.inv_mul_cancel, leviStar_one_apply, h1] at h2
  exact h2.symm

theorem planeVRepTw_radical (χ : RankOneCharacter) (r : RadicalLattice) (w : PlaneV n) :
    planeVRepTw n χ (identityPlaneRadicalInclusion r) w =
      realCoefficientComponent n χ (radicalUnipotentTw r).1 w := by
  change realCoefficientComponent n χ (ratReal (identityPlaneRadicalInclusion r).val) w = _
  rw [ratReal_radical_tw]

/-- **The cocycle law of the radical potential along the radical lattice.** -/
theorem planeRadical_radical_tw (χ : RankOneCharacter) (r : RadicalLattice) (g : PlaneStab) :
    planeRadical n χ (iwP (ratReal ((identityPlaneRadicalInclusion r).val * g.val))) =
      planeRadical n χ (radicalUnipotentTw r) +
        Representation.linHom (planeQRepTw n) (planeVRepTw n χ) (identityPlaneRadicalInclusion r)
          (planeRadical n χ (iwP (ratReal g.val))) := by
  apply LinearMap.ext
  intro Q
  rw [LinearMap.add_apply, linHom_radical_applyTw, planeVRepTw_radical]
  have hp : ratReal ((identityPlaneRadicalInclusion r).val * g.val) =
      (radicalUnipotentTw r).1 * ratReal g.val := by
    rw [map_mul, ratReal_radical_tw]
  rw [hp, planeRadical_iwP_mul χ (radicalUnipotentTw r) (ratReal g.val) Q, leviStar_radical_inv_tw]

end RadicalPotential

/-! ## The potentials of the twisted plane source -/

section Potentials

/-- **The potentials of the twisted plane source at the identity plane.** -/
def sourceCupDataTw {σ : CuspidalRepresentation} (E : LeviCocycleDataTw σ n)
    (χ : RankOneCharacter) : PlaneCupDataTw n χ where
  a x := E.α (iwA (ratReal x)) 1
  l x := planeRadical n χ (iwP (ratReal x))
  lam r := planeRadical n χ (radicalUnipotentTw r)
  a_radical r := by
    show E.α (iwA (ratReal (identityPlaneRadicalInclusion r).val)) 1 =
      E.α (iwA (ratReal (1 : RationalGL3))) 1
    rw [alpha_iwA_radical_tw E r, ratReal_one_tw, iwA_one_tw, alpha_one_tw E]
  l_radical r g := planeRadical_radical_tw χ r g

theorem sourceA_levi_tw {σ : CuspidalRepresentation} (E : LeviCocycleDataTw σ n)
    (χ : RankOneCharacter) (m : GeneralLinearGroup (Fin 2) ℤ) :
    (sourceCupDataTw E χ).a (identityPlaneLeviSection m).val - (sourceCupDataTw E χ).a 1 =
      E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1 := by
  show E.α (iwA (ratReal (identityPlaneLeviSection m).val)) 1 -
    E.α (iwA (ratReal (1 : RationalGL3))) 1 = _
  rw [ratReal_levi_tw, ratReal_one_tw, iwA_one_tw, alpha_one_tw E, sub_zero, alpha_iwA_levi_tw E]

/-- The twisted plane source at the identity adele and rational vertices is the cup product of the
potentials. -/
theorem sourceCupDataTw_identity (D : InducingData n) (E : LeviCocycleDataTw D.cusp n)
    (h3 : ConductorThree D.chi) (x : Fin 3 → RationalGL3) :
    planeSourceTw D E (fun i => ratReal (x i)) (rationalGroup (1 : RationalGL3)⁻¹) =
      ((sourceCupDataTw E D.chi).l (x 2) - (sourceCupDataTw E D.chi).l (x 1))
        ((sourceCupDataTw E D.chi).a (x 1) - (sourceCupDataTw E D.chi).a (x 0)) := by
  rw [_root_.inv_one, map_one]
  exact planeSourceTw_one D E h3 _

end Potentials

/-! ## The identity-plane coordinate of the twisted plane source -/

/-- **The identity-plane cusp coordinate of the twisted plane source is nonzero**, provided the
one-cocycle `m ↦ α(m) 1` of `GL₂(ℤ)` (the Levi cocycle at the identity adele) has nonzero class in
`H¹(GL₂(ℤ), arithmeticBinaryRep (n + 1) 0)`. -/
theorem planeSourceTw_cuspRes_identity_ne_zero (D : InducingData n)
    (E : LeviCocycleDataTw D.cusp n) (h3 : ConductorThree D.chi)
    (hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1) (pos : 0 < n) (odd : Odd n)
    (φ : groupCohomology.cocycles₁ (arithmeticBinaryRep (n + 1) 0))
    (hφ : ∀ m : GeneralLinearGroup (Fin 2) ℤ,
      (φ m : PlaneQ n) = E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1)
    (hφ0 : groupCohomology.H1π (arithmeticBinaryRep (n + 1) 0) φ ≠ 0)
    {z : cocycles rationalLevel
      (flagRepresentation (rationalCoefficientComponent n D.chi) .plane)}
    (hz : Evaluates D .plane (planeSourceTw D E) z) :
    TernaryPeriodPolynomials.Spectral.CuspReduction.cuspRes n D.chi .plane false
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n D.chi) .plane) z) ≠ 0 :=
  cuspRes_plane_false_ne_zero_of_evaluatesTw D hodd (sourceCupDataTw E D.chi)
    (kostantLawTw_of_planeRadical D.chi hodd (fun _ _ => rfl)) (neg_ne_zero.mpr one_ne_zero)
    φ (fun m => (hφ m).trans (sourceA_levi_tw E D.chi m).symm) hφ0 pos odd hz
    (sourceCupDataTw_identity D E h3)

/-! ## The twisted Eichler cocycle of an Eichler input -/

theorem isEichlerCocycleTw_eichlerCocycleTw {σ : CuspidalRepresentation}
    (D : EichlerInput σ n)
    (stages : PlaneEisensteinContinuation.AnalyticScalar.ContinuousStages σ) :
    IsEichlerCocycleTw σ n (eichlerCocycleTw D) :=
  ⟨eichlerCocycleTw_mul D stages, eichlerCocycleTw_orthogonal D,
    eichlerCocycleTw_binaryValues D stages,
    fun m => ⟨liftVectorTw D stages m, liftVectorTw_smooth D stages m,
      liftVectorTw_realize D stages m, liftVectorTw_spherical D stages m⟩,
    fun A m => eichlerCocycleTw_scalar_smooth D stages m A,
    eichlerCocycleTw_finiteLevel D stages⟩

/-! ## The final assembly -/

/-- **Source construction at the identity plane for the odd character of conductor three.**  If the
cuspidal representation of `D` has a `GL₂(ℤ̂)`-fixed vector and the character is a nontrivial
character of conductor three, then some summand class has a nonzero Shapiro coordinate at the
identity-plane cusp. -/
theorem sphericalSourceConstruction_of_conductorThree (D : InducingData n)
    (hχ : D.chi ≠ trivialCharacter) (h3 : ConductorThree D.chi) (_hne : associatePair D ≠ ⊥) :
    SphericalSourceConstruction D := by
  intro hsph
  have hodd : D.chi.toMonoidHom (realAdeleUnit (-1)) = -1 := chi_realNegOne_eq_neg_one hχ h3
  have hn : Odd n :=
    TernaryPeriodPolynomials.LevelOneCohomologicalParity.Helpers.cohomological_spherical_odd
      n D.cusp D.cohomological hsph
  have pos : 0 < n := hn.pos
  obtain ⟨Din⟩ := EichlerInput.nonempty_of_cohomological D.cusp hsph hn D.cohomological
  have stages := continuousStages D
  obtain ⟨φ, hφ, hφ0⟩ := eichlerCocycleTw_class_ne_zero Din stages hn
  obtain ⟨E, hE⟩ := exists_leviCocycleDataTw (isEichlerCocycleTw_eichlerCocycleTw Din stages)
  have hφE : ∀ m : GeneralLinearGroup (Fin 2) ℤ, (φ m : PlaneQ n) =
      E.α (GeneralLinearGroup.map (Int.castRingHom ℝ) m) 1 := by
    intro m
    rw [hE]
    exact hφ m
  have hsrc := planeSourceTw_isSourceCocycle D E h3 hodd
  refine (coordinateImage_ne_bot_iff D .plane false).mpr ⟨⟨planeSourceTw D E, hsrc⟩, ?_⟩
  have key := planeSourceTw_cuspRes_identity_ne_zero D E h3 hodd pos hn φ hφE hφ0
    (evaluatedSource_realizes D .plane ⟨planeSourceTw D E, hsrc⟩)
  exact key

end TernaryPeriodPolynomials.TwistedSource
