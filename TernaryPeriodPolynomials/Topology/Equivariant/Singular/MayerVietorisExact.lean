module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisSplitting

@[expose] public section

noncomputable section
namespace TernaryPoly.EquivariantSingularMayerVietoris
open CategoryTheory Limits HomologicalComplex EquivariantSingularSmall TopologicalSpace

variable {G : Type} [Group G]

/-- Evaluation of an actual biproduct lift is the lift of the evaluated maps. -/
theorem biprodEval_lift {K L M : ChainComplex (Rep ℚ G) ℕ} (a : K ⟶ L) (b : K ⟶ M) (n : ℕ) :
    (biprod.lift a b).f n ≫ (HomologicalComplex.biprodXIso L M n).hom = biprod.lift (a.f n) (b.f n) := by
  apply biprod.hom_ext
  · rw [Category.assoc, HomologicalComplex.biprodXIso_hom_fst, biprod.lift_fst]
    exact congrArg (fun f => f.f n) (biprod.lift_fst a b)
  · rw [Category.assoc, HomologicalComplex.biprodXIso_hom_snd, biprod.lift_snd]
    exact congrArg (fun f => f.f n) (biprod.lift_snd a b)

/-- Evaluation of an actual biproduct sum map is the sum of the evaluated maps. -/
theorem biprodEval_desc {K L M : ChainComplex (Rep ℚ G) ℕ} (a : L ⟶ K) (b : M ⟶ K) (n : ℕ) :
    (HomologicalComplex.biprodXIso L M n).inv ≫ (biprod.desc a b).f n = biprod.desc (a.f n) (b.f n) := by
  apply biprod.hom_ext'
  · rw [← Category.assoc, HomologicalComplex.inl_biprodXIso_inv, biprod.inl_desc]
    exact congrArg (fun f => f.f n) (biprod.inl_desc a b)
  · rw [← Category.assoc, HomologicalComplex.inr_biprodXIso_inv, biprod.inr_desc]
    exact congrArg (fun f => f.f n) (biprod.inr_desc a b)

variable (G) (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (U V : Opens E) (hU : InvariantSet G E (U : Set E)) (hV : InvariantSet G E (V : Set E))
  (hUV : U ⊔ V = ⊤)

/-- The evaluated actual Mayer–Vietoris chain sequence is isomorphic to its split degree sequence. -/
def degreeEvalIso (n : ℕ) :
    (chainShortComplex G E U V hU hV hUV).map (HomologicalComplex.eval (Rep ℚ G) (ComplexShape.down ℕ) n) ≅
      degreeShortComplex G E U V hU hV hUV n :=
  ShortComplex.isoMk (Iso.refl _) (HomologicalComplex.biprodXIso _ _ n) (Iso.refl _)
    (by
      change 𝟙 _ ≫ biprod.lift ((interToLeft G E U V hU hV).f n) (-((interToRight G E U V hU hV).f n)) =
        (biprod.lift (interToLeft G E U V hU hV) (-interToRight G E U V hU hV)).f n ≫
          (HomologicalComplex.biprodXIso _ _ n).hom
      rw [Category.id_comp, biprodEval_lift]
      rfl)
    (by
      change (HomologicalComplex.biprodXIso _ _ n).hom ≫
        biprod.desc ((leftToCover G E U V hU hV hUV).f n) ((rightToCover G E U V hU hV hUV).f n) =
          (biprod.desc (leftToCover G E U V hU hV hUV) (rightToCover G E U V hU hV hUV)).f n ≫ 𝟙 _
      rw [← biprodEval_desc, Iso.hom_inv_id_assoc, Category.comp_id])

/-- The actual evaluated chain sequence has a genuine equivariant splitting in every degree. -/
def evaluatedSplitting (n : ℕ) :
    ((chainShortComplex G E U V hU hV hUV).map
      (HomologicalComplex.eval (Rep ℚ G) (ComplexShape.down ℕ) n)).Splitting :=
  (degreeSplitting G E U V hU hV hUV n).ofIso (degreeEvalIso G E U V hU hV hUV n).symm

/-- Actual equivariant Mayer–Vietoris is degreewise short exact. -/
theorem evaluatedShortExact (n : ℕ) :
    ((chainShortComplex G E U V hU hV hUV).map
      (HomologicalComplex.eval (Rep ℚ G) (ComplexShape.down ℕ) n)).ShortExact :=
  (evaluatedSplitting G E U V hU hV hUV n).shortExact

/-- The genuine equivariant Mayer–Vietoris short exact sequence of actual subordinate/small chains. -/
theorem chainShortExact : (chainShortComplex G E U V hU hV hUV).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (evaluatedShortExact G E U V hU hV hUV)

end TernaryPoly.EquivariantSingularMayerVietoris
