module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisBiprod

@[expose] public section

noncomputable section
namespace TernaryPoly.EquivariantSingularMayerVietoris
open CategoryTheory Limits HomologicalComplex EquivariantSingularSmall TopologicalSpace

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (U V : Opens E) (hU : InvariantSet G E (U : Set E)) (hV : InvariantSet G E (V : Set E))
  (hUV : U ⊔ V = ⊤) (W : Rep.{0} ℚ G)

/-- Transport a genuine short complex through an isomorphism of its middle object. -/
def replaceMiddle {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
    {M : C} (e : S.X₂ ≅ M) : ShortComplex C :=
  ShortComplex.mk (S.f ≫ e.hom) (e.inv ≫ S.g) (by
    rw [Category.assoc, e.hom_inv_id_assoc]
    exact S.zero)

/-- The middle-object replacement retains the actual first and last maps under its isomorphism. -/
def replaceMiddleIso {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
    {M : C} (e : S.X₂ ≅ M) : S ≅ replaceMiddle S e :=
  ShortComplex.isoMk (Iso.refl _) e (Iso.refl _)
    (by simp [replaceMiddle]) (by simp [replaceMiddle])

/-- The actual cochain Mayer–Vietoris sequence with the two open-set terms separated. -/
def separatedShortComplex : ShortComplex (CochainComplex (ModuleCat ℚ) ℕ) :=
  replaceMiddle (cochainShortComplex G E U V hU hV hUV W)
    (homBiprodIso (leftChains G E U hU) (rightChains G E V hV) W)

/-- The explicit Hom biproduct comparison identifies the two versions of the actual sequence. -/
def separatedIso : cochainShortComplex G E U V hU hV hUV W ≅
    separatedShortComplex G E U V hU hV hUV W :=
  replaceMiddleIso _ _

/-- The separated actual cochain sequence is short exact. -/
theorem separatedShortExact : (separatedShortComplex G E U V hU hV hUV W).ShortExact :=
  ShortComplex.shortExact_of_iso (separatedIso G E U V hU hV hUV W)
    (cochainShortExact G E U V hU hV hUV W)

/-- The first actual cochain map is exactly the pair of restrictions. -/
theorem separated_f : (separatedShortComplex G E U V hU hV hUV W).f =
    biprod.lift (homPullback (leftToCover G E U V hU hV hUV) W)
      (homPullback (rightToCover G E U V hU hV hUV) W) :=
  homBiprodIso_restriction _ _ W

/-- The second actual cochain map is exactly left restriction minus right restriction. -/
theorem separated_g : (separatedShortComplex G E U V hU hV hUV W).g =
    biprod.desc (homPullback (interToLeft G E U V hU hV) W)
      (-homPullback (interToRight G E U V hU hV) W) :=
  homBiprodIso_difference _ _ W

end TernaryPoly.EquivariantSingularMayerVietoris
