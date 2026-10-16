module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Singular.Orbit
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.FrozenMeasure
public import TernaryPeriodPolynomials.DifferentialForm.Principal.CompactForget

@[expose] public section


/-!
# The deck group and its subgroups: Shapiro for the singular compact-to-ordinary map

The deck group `FDeck = principalSixInK` is isomorphic (`deckEquiv`) to the cover
`gamma0 = principalSixInKReal ≤ GL₃(ℝ)`.  A subgroup `H ≤ gamma0` embeds into `FDeck`
(`toDeck`), with finite index in `FDeck` as soon as it has finite index in `gamma0`
(`finite_deck_quotient`), and `orbitMapDeck : OrbitSpace H → FOrbit` is the map of orbit spaces.
`singularVanish_of_deck_ind` is Shapiro for the actual singular compact-to-ordinary map: vanishing
for the deck group with the induced coefficients `indRep (toDeck hle) V` gives vanishing for the cover
of `H` with coefficients `Rep.res (toDeck hle) V`.

Formalized by Claude Sonnet 5.5.
-/


open TopologicalSpace CategoryTheory

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.SymmetricSpaceArithmeticProper TernaryPoly.CompactInteriorRelativeBoundary

/-- The deck element as a monoid homomorphism into `gamma0`. -/
def toGammaHom : FDeck →* gamma0 where
  toFun := toGamma
  map_one' := Subtype.ext (map_one TernaryPoly.PolynomialCoefficientMetric.deckMatrix)
  map_mul' g h := Subtype.ext (map_mul TernaryPoly.PolynomialCoefficientMetric.deckMatrix g h)

theorem toGammaHom_injective : Function.Injective toGammaHom := by
  intro g h hgh
  have h1 : TernaryPoly.PolynomialCoefficientMetric.deckMatrix g =
      TernaryPoly.PolynomialCoefficientMetric.deckMatrix h := congrArg Subtype.val hgh
  exact deckInclusion_injective (realIntegral_injective h1)

/-- The deck group is isomorphic to the cover `gamma0` as a subgroup of `GL₃(ℝ)`. -/
def deckEquiv : FDeck ≃* gamma0 :=
  MulEquiv.ofBijective toGammaHom ⟨toGammaHom_injective, toGamma_surjective⟩

theorem deckEquiv_apply (g : FDeck) : deckEquiv g = toGamma g := rfl


section Shapiro

variable {H : Subgroup RealGL} (hle : H ≤ gamma0)

/-- The inclusion of a subgroup of the cover into the deck group. -/
def toDeck : H →* FDeck :=
  (deckEquiv.symm : gamma0 →* FDeck).comp (Subgroup.inclusion hle)

theorem toDeck_smul (h : H) (x : Space) : (toDeck hle h) • x = (h : RealGL) • x := by
  change toGamma (toDeck hle h) • x = _
  have : toGamma (toDeck hle h) = Subgroup.inclusion hle h := by
    change deckEquiv (deckEquiv.symm (Subgroup.inclusion hle h)) = _
    exact deckEquiv.apply_symm_apply _
  rw [this]
  rfl

theorem finite_deck_quotient [Finite (gamma0 ⧸ H.subgroupOf gamma0)] :
    Finite (FDeck ⧸ (toDeck hle).range) := by
  have e : (toDeck hle).range = (H.subgroupOf gamma0).comap toGammaHom := by
    ext d
    constructor
    · rintro ⟨h, rfl⟩
      change toGamma (toDeck hle h) ∈ H.subgroupOf gamma0
      have : toGamma (toDeck hle h) = Subgroup.inclusion hle h := by
        change deckEquiv (deckEquiv.symm (Subgroup.inclusion hle h)) = _
        exact deckEquiv.apply_symm_apply _
      rw [this]
      exact h.2
    · intro hd
      have hd' : (toGammaHom d : gamma0).1 ∈ H := hd
      refine ⟨⟨(toGammaHom d).1, hd'⟩, ?_⟩
      apply deckEquiv.injective
      have : deckEquiv (toDeck hle ⟨(toGammaHom d).1, hd'⟩) = Subgroup.inclusion hle ⟨(toGammaHom d).1, hd'⟩ := by
        change deckEquiv (deckEquiv.symm (Subgroup.inclusion hle _)) = _
        exact deckEquiv.apply_symm_apply _
      rw [this]
      rfl
  rw [e]
  have hidx : ((H.subgroupOf gamma0).comap toGammaHom).index = (H.subgroupOf gamma0).index :=
    Subgroup.index_comap_of_surjective _ toGamma_surjective
  have : (H.subgroupOf gamma0).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hfi : ((H.subgroupOf gamma0).comap toGammaHom).FiniteIndex := ⟨by rw [hidx]; exact this⟩
  exact Subgroup.finite_quotient_of_finiteIndex


/-- The map of orbit spaces from a subgroup of the cover to the deck-group orbit space. -/
def orbitMapDeck : OrbitSpace H → FOrbit :=
  Quotient.map' id (fun S T h => by
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp h
    exact MulAction.orbitRel_apply.mpr ⟨toDeck hle g, by
      change toDeck hle g • T = S
      rw [toDeck_smul]; exact hg⟩)

theorem continuous_orbitMapDeck : Continuous (orbitMapDeck hle) := by
  apply Continuous.quotient_lift
  exact continuous_quotient_mk'

/-- **Shapiro for the cover.**  Vanishing of the actual compact-to-ordinary map of the deck
group with the induced coefficients gives vanishing for an admissible subgroup of the cover. -/
theorem singularVanish_of_deck_ind (hH : Admissible H) (V : Rep.{0} ℚ FDeck)
    (h : letI : Fact (IsQuotientCoveringMap singularCoveringProjection FDeck) :=
        ⟨quotientProjection_quotientCovering⟩
      compactForget singularCoveringProjection (indRep (toDeck hle) V) 2 = 0) :
    SingularVanish H hH (Rep.res (toDeck hle) V) := by
  let _ : Fact (IsQuotientCoveringMap singularCoveringProjection FDeck) :=
    ⟨quotientProjection_quotientCovering⟩
  let _ : Fact (IsQuotientCoveringMap (coverHom H) H) := ⟨hH.quotientCovering⟩
  change compactForget (coverHom H) (Rep.res (toDeck hle) V) 2 = 0
  exact compactForget_zero_res_of_ind (toDeck hle) (fun x y => (toDeck_smul hle x y).symm)
    singularCoveringProjection (coverHom H)
    (TopCat.ofHom ⟨orbitMapDeck hle, continuous_orbitMapDeck hle⟩) rfl V h

end Shapiro

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
