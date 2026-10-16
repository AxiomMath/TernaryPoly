module

public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisComponents

@[expose] public section

noncomputable section
namespace TernaryPoly.EquivariantSingularMayerVietoris
open CategoryTheory Limits FreeActionLinearization EquivariantSingularSmall
open SphereOddDegree TopologicalSpace

variable (G : Type) [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (U V : Opens E) (hU : InvariantSet G E (U : Set E)) (hV : InvariantSet G E (V : Set E))
  (hUV : U ⊔ V = ⊤)

/-- The actual degreewise Mayer–Vietoris short complex in representations. -/
def degreeShortComplex (n : ℕ) : ShortComplex (Rep ℚ G) :=
  ShortComplex.mk
    (biprod.lift ((interToLeft G E U V hU hV).f n) (-((interToRight G E U V hU hV).f n)))
    (biprod.desc ((leftToCover G E U V hU hV hUV).f n) ((rightToCover G E U V hU hV hUV).f n))
    (by
      rw [biprod.lift_desc]
      have h := congrArg (fun m => m.f n) (inclusion_square G E U V hU hV hUV)
      change (interToLeft G E U V hU hV).f n ≫ (leftToCover G E U V hU hV hUV).f n =
        (interToRight G E U V hU hV).f n ≫ (rightToCover G E U V hU hV hUV).f n at h
      rw [h]
      exact add_neg_cancel _)

/-- The genuine equivariant graded retraction includes the prescribed minus sign. -/
def degreeRetraction (n : ℕ) :
    (leftChains G E U hU).X n ⊞ (rightChains G E V hV).X n ⟶ (interChains G E U V hU hV).X n :=
  -(biprod.snd ≫ projectRightToInter G E U V hU hV n)

/-- The genuine equivariant graded section routes each small simplex to its left or right-only part. -/
def degreeSection (n : ℕ) :
    (coverChains G E U V hU hV hUV).X n ⟶ (leftChains G E U hU).X n ⊞ (rightChains G E V hV).X n :=
  biprod.lift (routeLeft G E U V hU hV hUV n) (routeRight G E U V hU hV hUV n)

/-- The signed actual graded retraction is a left inverse of the Mayer–Vietoris left map. -/
theorem degree_f_r (n : ℕ) :
    (degreeShortComplex G E U V hU hV hUV n).f ≫ degreeRetraction G E U V hU hV n = 𝟙 _ := by
  change biprod.lift ((interToLeft G E U V hU hV).f n) (-((interToRight G E U V hU hV).f n)) ≫
    (-(biprod.snd ≫ projectRightToInter G E U V hU hV n)) = 𝟙 _
  erw [Preadditive.comp_neg, ← Category.assoc, biprod.lift_snd, Preadditive.neg_comp, neg_neg]
  exact inter_projectRight G E U V hU hV hUV n

/-- The actual coordinate-routing section is a right inverse of the Mayer–Vietoris sum map. -/
theorem degree_s_g (n : ℕ) :
    degreeSection G E U V hU hV hUV n ≫ (degreeShortComplex G E U V hU hV hUV n).g = 𝟙 _ := by
  change biprod.lift (routeLeft G E U V hU hV hUV n) (routeRight G E U V hU hV hUV n) ≫
    biprod.desc ((leftToCover G E U V hU hV hUV).f n) ((rightToCover G E U V hU hV hUV).f n) = 𝟙 _
  rw [biprod.lift_desc]
  exact route_cover_identity G E U V hU hV hUV n

/-- A representation-valued biproduct splitting identity, derived from its four actual matrix components. -/
theorem biprodSplittingIdentity {A B C D : Rep ℚ G}
    (a : C ⟶ A) (b : C ⟶ B) (u : A ⟶ D) (v : B ⟶ D)
    (p : B ⟶ C) (q : D ⟶ A) (r : D ⟶ B)
    (hu : u ≫ q = 𝟙 A) (hr : u ≫ r = 0)
    (hv : v ≫ q = p ≫ a) (hb : p ≫ b + v ≫ r = 𝟙 B) :
    (-(biprod.snd ≫ p)) ≫ biprod.lift a (-b) +
      biprod.desc u v ≫ biprod.lift q r = 𝟙 (A ⊞ B) := by
  apply biprod.hom_ext' <;> apply biprod.hom_ext
  · simp [Category.assoc, Preadditive.comp_add, hu]
  · simp [Category.assoc, Preadditive.comp_add, hr]
  · simp [Category.assoc, Preadditive.comp_add, Preadditive.add_comp, hv]
  · simpa [Category.assoc, Preadditive.comp_add, Preadditive.add_comp] using hb

/-- The actual equivariant retraction and section satisfy the graded splitting identity. -/
theorem degree_split_identity (n : ℕ) :
    (degreeRetraction G E U V hU hV n ≫ (degreeShortComplex G E U V hU hV hUV n).f :
      (degreeShortComplex G E U V hU hV hUV n).X₂ ⟶ (degreeShortComplex G E U V hU hV hUV n).X₂) +
      ((degreeShortComplex G E U V hU hV hUV n).g ≫ degreeSection G E U V hU hV hUV n :
        (degreeShortComplex G E U V hU hV hUV n).X₂ ⟶ (degreeShortComplex G E U V hU hV hUV n).X₂) =
      𝟙 (degreeShortComplex G E U V hU hV hUV n).X₂ :=
  biprodSplittingIdentity G ((interToLeft G E U V hU hV).f n) ((interToRight G E U V hU hV).f n)
    ((leftToCover G E U V hU hV hUV).f n) ((rightToCover G E U V hU hV hUV).f n)
    (projectRightToInter G E U V hU hV n) (routeLeft G E U V hU hV hUV n) (routeRight G E U V hU hV hUV n)
    (left_routeLeft G E U V hU hV hUV n) (left_routeRight G E U V hU hV hUV n)
    (right_routeLeft G E U V hU hV hUV n) (right_inter_add_route G E U V hU hV hUV n)

/-- A genuine degreewise equivariant splitting of the actual Mayer–Vietoris short complex. -/
def degreeSplitting (n : ℕ) : (degreeShortComplex G E U V hU hV hUV n).Splitting where
  r := degreeRetraction G E U V hU hV n
  s := degreeSection G E U V hU hV hUV n
  f_r := degree_f_r G E U V hU hV hUV n
  s_g := degree_s_g G E U V hU hV hUV n
  id := degree_split_identity G E U V hU hV hUV n

/-- The actual degreewise representation-valued Mayer–Vietoris short complex is short exact. -/
theorem degreeShortExact (n : ℕ) : (degreeShortComplex G E U V hU hV hUV n).ShortExact :=
  (degreeSplitting G E U V hU hV hUV n).shortExact

end TernaryPoly.EquivariantSingularMayerVietoris
