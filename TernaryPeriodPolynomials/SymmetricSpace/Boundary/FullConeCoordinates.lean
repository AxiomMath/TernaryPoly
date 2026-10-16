module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullCanonicalCone

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory Category Limits HomologicalComplex Preadditive Linear

section Generic
variable {G : Type} [Group G]

/-- Linear precomposition by an actual representation isomorphism. -/
def repHomIso {X Y : Rep.{0} ℚ G} (e : X ≅ Y) (W : Rep.{0} ℚ G) :
    (X ⟶ W) ≃ₗ[ℚ] (Y ⟶ W) where
  toFun f := e.inv ≫ f
  invFun f := e.hom ≫ f
  left_inv f := by simp
  right_inv f := by simp
  map_add' f g := by simp only [comp_add]
  map_smul' r f := by simp only [comp_smul]; rfl

/-- Literal pair of restrictions of a morphism out of a biproduct. -/
def repBiprodHom (X Y W : Rep.{0} ℚ G) :
    (X ⊞ Y ⟶ W) ≃ₗ[ℚ] (X ⟶ W) × (Y ⟶ W) where
  toFun f := (biprod.inl ≫ f,biprod.inr ≫ f)
  invFun p := biprod.desc p.1 p.2
  left_inv f := by apply biprod.hom_ext' <;> simp
  right_inv p := by simp
  map_add' f g := by simp only [comp_add]; rfl
  map_smul' r f := by simp only [comp_smul]; rfl

variable {F L P : ChainComplex (Rep.{0} ℚ G) ℕ}
  (a : F ⟶ L) (b : F ⟶ P) (W : Rep.{0} ℚ G)

abbrev signedArrow := biprod.lift a (-b)
abbrev signedCone := homotopyCofiber (signedArrow a b)

theorem downSucc (n : ℕ) : (ComplexShape.down ℕ).Rel (n+1) n := rfl

theorem downZero : ¬ (ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) := by
  simp [ComplexShape.down_Rel]

/-- Degree zero has only the two actual face components. -/
def signedConeHomZero : ((signedCone a b).X 0 ⟶ W) ≃ₗ[ℚ] (L.X 0 ⟶ W) × (P.X 0 ⟶ W) :=
  (repHomIso (homotopyCofiber.XIso (signedArrow a b) 0 downZero) W).trans
    ((repHomIso (HomologicalComplex.biprodXIso L P 0) W).trans (repBiprodHom _ _ W))

/-- Positive degree consists of one corner component and the two actual face components. -/
def signedConeHomSucc (n : ℕ) : ((signedCone a b).X (n+1) ⟶ W) ≃ₗ[ℚ]
    (F.X n ⟶ W) × ((L.X (n+1) ⟶ W) × (P.X (n+1) ⟶ W)) :=
  (repHomIso (homotopyCofiber.XIsoBiprod (signedArrow a b) (n+1) n (downSucc n)) W).trans
    ((repBiprodHom _ _ W).trans
      (LinearEquiv.prodCongr (LinearEquiv.refl ℚ _) ((repHomIso
        (HomologicalComplex.biprodXIso L P (n+1)) W).trans (repBiprodHom _ _ W))))

/-- Literal line and plane inclusions in a degree of the cone. -/
def signedLineInclusion (n : ℕ) : L.X n ⟶ (signedCone a b).X n :=
  (biprod.inl : L ⟶ L ⊞ P).f n ≫ homotopyCofiber.inrX (signedArrow a b) n

def signedPlaneInclusion (n : ℕ) : P.X n ⟶ (signedCone a b).X n :=
  (biprod.inr : P ⟶ L ⊞ P).f n ≫ homotopyCofiber.inrX (signedArrow a b) n

def signedCornerInclusion (n : ℕ) : F.X n ⟶ (signedCone a b).X (n+1) :=
  homotopyCofiber.inlX (signedArrow a b) n (n+1) (downSucc n)

theorem signedConeHomZero_apply (c : (signedCone a b).X 0 ⟶ W) :
    signedConeHomZero a b W c = (signedLineInclusion a b 0 ≫ c,signedPlaneInclusion a b 0 ≫ c) := by
  dsimp [signedConeHomZero,repHomIso,repBiprodHom,signedLineInclusion,signedPlaneInclusion]
  simp only [← Category.assoc,inl_biprodXIso_inv,inr_biprodXIso_inv]
  rfl

theorem signedConeHomSucc_apply (n : ℕ) (c : (signedCone a b).X (n+1) ⟶ W) :
    signedConeHomSucc a b W n c = (signedCornerInclusion a b n ≫ c,
      (signedLineInclusion a b (n+1) ≫ c,signedPlaneInclusion a b (n+1) ≫ c)) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · change biprod.inl ≫ (biprodXIso L P (n+1)).inv ≫ biprod.inr ≫
      (homotopyCofiber.XIsoBiprod (signedArrow a b) (n+1) n (downSucc n)).inv ≫ c = _
    rw [←Category.assoc,inl_biprodXIso_inv]
    simp only [←Category.assoc,homotopyCofiber.inr_XIsoBiprod_inv]
    rfl
  · change biprod.inr ≫ (biprodXIso L P (n+1)).inv ≫ biprod.inr ≫
      (homotopyCofiber.XIsoBiprod (signedArrow a b) (n+1) n (downSucc n)).inv ≫ c = _
    rw [←Category.assoc,inr_biprodXIso_inv]
    simp only [←Category.assoc,homotopyCofiber.inr_XIsoBiprod_inv]
    rfl

/-- Face inclusions retain the actual bar differentials. -/
theorem signedLineInclusion_d (i j : ℕ) :
    signedLineInclusion a b i ≫ (signedCone a b).d i j = L.d i j ≫ signedLineInclusion a b j :=
  ((biprod.inl : L ⟶ L ⊞ P) ≫ homotopyCofiber.inr (signedArrow a b)).comm i j

theorem signedPlaneInclusion_d (i j : ℕ) :
    signedPlaneInclusion a b i ≫ (signedCone a b).d i j = P.d i j ≫ signedPlaneInclusion a b j :=
  ((biprod.inr : P ⟶ L ⊞ P) ≫ homotopyCofiber.inr (signedArrow a b)).comm i j

theorem signedArrow_component (n : ℕ) :
    (signedArrow a b).f n ≫ homotopyCofiber.inrX (signedArrow a b) n =
    a.f n ≫ signedLineInclusion a b n - b.f n ≫ signedPlaneInclusion a b n := by
  simp only [signedArrow,biprod.lift_eq,add_f_apply,comp_f,neg_f_apply,
    add_comp,neg_comp,signedLineInclusion,signedPlaneInclusion,Category.assoc,sub_eq_add_neg]

/-- The bottom corner maps to line minus plane, with no shifted corner term. -/
theorem signedCornerInclusion_d_zero :
    signedCornerInclusion a b 0 ≫ (signedCone a b).d 1 0 =
    a.f 0 ≫ signedLineInclusion a b 0 - b.f 0 ≫ signedPlaneInclusion a b 0 :=
  (homotopyCofiber.inlX_d' (signedArrow a b) 1 0 (downSucc 0) downZero).trans
    (signedArrow_component a b 0)

/-- The shifted corner differential carries its canonical minus sign. -/
theorem signedCornerInclusion_d_succ (n : ℕ) :
    signedCornerInclusion a b (n+1) ≫ (signedCone a b).d (n+2) (n+1) =
    -F.d (n+1) n ≫ signedCornerInclusion a b n +
      (a.f (n+1) ≫ signedLineInclusion a b (n+1) - b.f (n+1) ≫ signedPlaneInclusion a b (n+1)) :=
  (homotopyCofiber.inlX_d (signedArrow a b) (n+2) (n+1) n (downSucc (n+1)) (downSucc n)).trans
    (congrArg (fun z => -F.d (n+1) n ≫ signedCornerInclusion a b n + z)
      (signedArrow_component a b (n+1)))

end Generic
end TernaryPoly.SymmetricSpaceBoundaryFull
