module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisExact

@[expose] public section


noncomputable section
namespace TernaryPoly.EquivariantSingularMayerVietoris
open CategoryTheory Limits HomologicalComplex EquivariantSingularSmall TopologicalSpace

variable {G : Type} [Group G]

/-- Genuine Hom cochains reverse an actual chain short complex. -/
def homShortComplex (S : ShortComplex (ChainComplex (Rep ℚ G) ℕ)) (W : Rep.{0} ℚ G) :
    ShortComplex (CochainComplex (ModuleCat ℚ) ℕ) :=
  ShortComplex.mk (homPullback S.g W) (homPullback S.f W) (by
    rw [← homPullback_comp, S.zero]
    apply HomologicalComplex.hom_ext
    intro n
    ext c
    change S.X₃.X n ⟶ W at c
    change (0 : S.X₁.X n ⟶ S.X₃.X n) ≫ c = 0
    simp only [zero_comp])

/-- Evaluation commutes with the genuine reversed Hom construction. -/
def homDegreeIso (S : ShortComplex (ChainComplex (Rep ℚ G) ℕ)) (W : Rep.{0} ℚ G) (n : ℕ) :
    (((S.map (HomologicalComplex.eval (Rep ℚ G) (ComplexShape.down ℕ) n)).map
      ((linearYoneda ℚ (Rep ℚ G)).obj W).rightOp).unop) ≅
      (homShortComplex S W).map (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.up ℕ) n) :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp; rfl) (by simp; rfl)

/-- Every equivariant graded splitting gives a genuine Hom-cochain graded splitting. -/
def homDegreeSplitting (S : ShortComplex (ChainComplex (Rep ℚ G) ℕ)) (W : Rep.{0} ℚ G) (n : ℕ)
    (s : (S.map (HomologicalComplex.eval (Rep ℚ G) (ComplexShape.down ℕ) n)).Splitting) :
    ((homShortComplex S W).map
      (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.up ℕ) n)).Splitting :=
  ((s.map ((linearYoneda ℚ (Rep ℚ G)).obj W).rightOp).unop).ofIso (homDegreeIso S W n)

/-- Genuine Hom sends degreewise split chain sequences to short exact cochain sequences. -/
theorem homShortExact (S : ShortComplex (ChainComplex (Rep ℚ G) ℕ)) (W : Rep.{0} ℚ G)
    (s : ∀ n, (S.map (HomologicalComplex.eval (Rep ℚ G) (ComplexShape.down ℕ) n)).Splitting) :
    (homShortComplex S W).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n => (homDegreeSplitting S W n (s n)).shortExact)

variable (G) (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (U V : Opens E) (hU : InvariantSet G E (U : Set E)) (hV : InvariantSet G E (V : Set E))
  (hUV : U ⊔ V = ⊤) (W : Rep.{0} ℚ G)

/-- Actual Mayer–Vietoris Hom-cochain sequence for arbitrary rational representations. -/
def cochainShortComplex : ShortComplex (CochainComplex (ModuleCat ℚ) ℕ) :=
  homShortComplex (chainShortComplex G E U V hU hV hUV) W

/-- The actual equivariant Mayer–Vietoris cochain sequence is short exact. -/
theorem cochainShortExact : (cochainShortComplex G E U V hU hV hUV W).ShortExact :=
  homShortExact _ W (evaluatedSplitting G E U V hU hV hUV)

end TernaryPoly.EquivariantSingularMayerVietoris
