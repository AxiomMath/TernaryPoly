module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.DiagSystem
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

@[expose] public section


/-!
# The homotopy pushout cone of two chain maps

For chain maps `a : A ⟶ L` and `b : A ⟶ P` of complexes of representations, the cone `K` of the signed arrow
`biprod.lift a (-b) : A ⟶ L ⊞ P` is the homotopy pushout of `L ← A → P`.  `PushCone` records the three
"coordinate" inclusions `iA`, `iL`, `iP`, the decomposition of the terms of `K` into them, and the differential of
`K` on them; `pushConeOfCofiber` shows that Mathlib's `homotopyCofiber` has this structure.  This presentation
avoids the dependent biprod bookkeeping in later constructions (diagonals, carriers).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]

/-- The coordinate presentation of a homotopy pushout cone. -/
structure PushCone (A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ) (a : A ⟶ L) (b : A ⟶ P) where
  iA : ∀ n, A.X n ⟶ K.X (n+1)
  iL : ∀ n, L.X n ⟶ K.X n
  iP : ∀ n, P.X n ⟶ K.X n
  desc0 : ∀ {Z : Rep.{0} ℚ Γ}, (L.X 0 ⟶ Z) → (P.X 0 ⟶ Z) → (K.X 0 ⟶ Z)
  desc : ∀ (n : ℕ) {Z : Rep.{0} ℚ Γ}, (A.X n ⟶ Z) → (L.X (n+1) ⟶ Z) → (P.X (n+1) ⟶ Z) → (K.X (n+1) ⟶ Z)
  iL0_desc0 : ∀ {Z : Rep.{0} ℚ Γ} (f : L.X 0 ⟶ Z) (g : P.X 0 ⟶ Z), iL 0 ≫ desc0 f g = f
  iP0_desc0 : ∀ {Z : Rep.{0} ℚ Γ} (f : L.X 0 ⟶ Z) (g : P.X 0 ⟶ Z), iP 0 ≫ desc0 f g = g
  ext0 : ∀ {Z : Rep.{0} ℚ Γ} {f g : K.X 0 ⟶ Z}, iL 0 ≫ f = iL 0 ≫ g → iP 0 ≫ f = iP 0 ≫ g → f = g
  iA_desc : ∀ (n : ℕ) {Z : Rep.{0} ℚ Γ} (f : A.X n ⟶ Z) (g : L.X (n+1) ⟶ Z) (h : P.X (n+1) ⟶ Z),
    iA n ≫ desc n f g h = f
  iL_desc : ∀ (n : ℕ) {Z : Rep.{0} ℚ Γ} (f : A.X n ⟶ Z) (g : L.X (n+1) ⟶ Z) (h : P.X (n+1) ⟶ Z),
    iL (n+1) ≫ desc n f g h = g
  iP_desc : ∀ (n : ℕ) {Z : Rep.{0} ℚ Γ} (f : A.X n ⟶ Z) (g : L.X (n+1) ⟶ Z) (h : P.X (n+1) ⟶ Z),
    iP (n+1) ≫ desc n f g h = h
  ext : ∀ (n : ℕ) {Z : Rep.{0} ℚ Γ} {f g : K.X (n+1) ⟶ Z}, iA n ≫ f = iA n ≫ g →
    iL (n+1) ≫ f = iL (n+1) ≫ g → iP (n+1) ≫ f = iP (n+1) ≫ g → f = g
  dL : ∀ n, iL (n+1) ≫ K.d (n+1) n = L.d (n+1) n ≫ iL n
  dP : ∀ n, iP (n+1) ≫ K.d (n+1) n = P.d (n+1) n ≫ iP n
  dA0 : iA 0 ≫ K.d 1 0 = a.f 0 ≫ iL 0 - b.f 0 ≫ iP 0
  dA : ∀ n, iA (n+1) ≫ K.d (n+2) (n+1) =
    -(A.d (n+1) n ≫ iA n) + a.f (n+1) ≫ iL (n+1) - b.f (n+1) ≫ iP (n+1)

section Cofiber

variable {A L P : ChainComplex (Rep.{0} ℚ Γ) ℕ} (a : A ⟶ L) (b : A ⟶ P)

/-- The signed arrow into the biproduct. -/
abbrev pushArrow : A ⟶ L ⊞ P := biprod.lift a (-b)

/-- The homotopy pushout cone. -/
abbrev pushCone : ChainComplex (Rep.{0} ℚ Γ) ℕ := HomologicalComplex.homotopyCofiber (pushArrow a b)

open HomologicalComplex in
theorem down_rel_succ (n : ℕ) : (ComplexShape.down ℕ).Rel (n+1) n := rfl

open HomologicalComplex in
theorem down_not_rel_zero : ¬ (ComplexShape.down ℕ).Rel 0 ((ComplexShape.down ℕ).next 0) := by
  simp [ComplexShape.down_Rel]

open HomologicalComplex in
/-- The coordinate inclusion `L ⟶ cone`. -/
def coneIL (n : ℕ) : L.X n ⟶ (pushCone a b).X n :=
  (biprod.inl : L ⟶ L ⊞ P).f n ≫ homotopyCofiber.inrX (pushArrow a b) n

open HomologicalComplex in
/-- The coordinate inclusion `P ⟶ cone`. -/
def coneIP (n : ℕ) : P.X n ⟶ (pushCone a b).X n :=
  (biprod.inr : P ⟶ L ⊞ P).f n ≫ homotopyCofiber.inrX (pushArrow a b) n

open HomologicalComplex in
/-- The coordinate inclusion `A ⟶ cone` (shifted). -/
def coneIA (n : ℕ) : A.X n ⟶ (pushCone a b).X (n+1) :=
  homotopyCofiber.inlX (pushArrow a b) n (n+1) (down_rel_succ n)

open HomologicalComplex in
def coneDesc0 {Z : Rep.{0} ℚ Γ} (f : L.X 0 ⟶ Z) (g : P.X 0 ⟶ Z) : (pushCone a b).X 0 ⟶ Z :=
  (homotopyCofiber.XIso (pushArrow a b) 0 down_not_rel_zero).hom ≫ (biprodXIso L P 0).hom ≫ biprod.desc f g

open HomologicalComplex in
def coneDesc (n : ℕ) {Z : Rep.{0} ℚ Γ} (f : A.X n ⟶ Z) (g : L.X (n+1) ⟶ Z) (h : P.X (n+1) ⟶ Z) :
    (pushCone a b).X (n+1) ⟶ Z :=
  (homotopyCofiber.XIsoBiprod (pushArrow a b) (n+1) n (down_rel_succ n)).hom ≫
    biprod.desc f ((biprodXIso L P (n+1)).hom ≫ biprod.desc g h)

open HomologicalComplex in
theorem pushArrow_f (n : ℕ) : (pushArrow a b).f n =
    a.f n ≫ (biprod.inl : L ⟶ L ⊞ P).f n - b.f n ≫ (biprod.inr : P ⟶ L ⊞ P).f n := by
  apply biprodX_ext_to
  · simp [biprod_lift_fst_f]
  · simp [biprod_lift_snd_f]

open HomologicalComplex in
theorem inl_f_biprodXIso_hom (n : ℕ) :
    (biprod.inl : L ⟶ L ⊞ P).f n ≫ (biprodXIso L P n).hom = biprod.inl := by
  calc (biprod.inl : L ⟶ L ⊞ P).f n ≫ (biprodXIso L P n).hom
      = (biprod.inl ≫ (biprodXIso L P n).inv) ≫ (biprodXIso L P n).hom := by
        rw [inl_biprodXIso_inv]
    _ = biprod.inl := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

open HomologicalComplex in
theorem inr_f_biprodXIso_hom (n : ℕ) :
    (biprod.inr : P ⟶ L ⊞ P).f n ≫ (biprodXIso L P n).hom = biprod.inr := by
  calc (biprod.inr : P ⟶ L ⊞ P).f n ≫ (biprodXIso L P n).hom
      = (biprod.inr ≫ (biprodXIso L P n).inv) ≫ (biprodXIso L P n).hom := by
        rw [inr_biprodXIso_inv]
    _ = biprod.inr := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

open HomologicalComplex in
theorem coneIA_desc (n : ℕ) {Z : Rep.{0} ℚ Γ} (f : A.X n ⟶ Z) (g : L.X (n+1) ⟶ Z) (h : P.X (n+1) ⟶ Z) :
    coneIA a b n ≫ coneDesc a b n f g h = f := by
  unfold coneIA coneDesc
  rw [homotopyCofiber.inlX_XIsoBiprod_hom_assoc]
  simp

open HomologicalComplex in
theorem coneIL_desc (n : ℕ) {Z : Rep.{0} ℚ Γ} (f : A.X n ⟶ Z) (g : L.X (n+1) ⟶ Z) (h : P.X (n+1) ⟶ Z) :
    coneIL a b (n+1) ≫ coneDesc a b n f g h = g := by
  unfold coneIL coneDesc
  rw [Category.assoc, homotopyCofiber.inrX_XIsoBiprod_hom_assoc (pushArrow a b) n (n+1) (down_rel_succ n)]
  simp only [biprod.inr_desc]
  rw [← Category.assoc, inl_f_biprodXIso_hom]
  simp

open HomologicalComplex in
theorem coneIP_desc (n : ℕ) {Z : Rep.{0} ℚ Γ} (f : A.X n ⟶ Z) (g : L.X (n+1) ⟶ Z) (h : P.X (n+1) ⟶ Z) :
    coneIP a b (n+1) ≫ coneDesc a b n f g h = h := by
  unfold coneIP coneDesc
  rw [Category.assoc, homotopyCofiber.inrX_XIsoBiprod_hom_assoc (pushArrow a b) n (n+1) (down_rel_succ n)]
  simp only [biprod.inr_desc]
  rw [← Category.assoc, inr_f_biprodXIso_hom]
  simp

open HomologicalComplex in
@[reassoc]
theorem inrX_zero_comp_XIso :
    homotopyCofiber.inrX (pushArrow a b) 0 ≫ (homotopyCofiber.XIso (pushArrow a b) 0 down_not_rel_zero).hom = 𝟙 _ := by
  unfold homotopyCofiber.inrX
  rw [dite_eq_right down_not_rel_zero]
  exact Iso.inv_hom_id _

open HomologicalComplex in
theorem coneIL_desc0 {Z : Rep.{0} ℚ Γ} (f : L.X 0 ⟶ Z) (g : P.X 0 ⟶ Z) :
    coneIL a b 0 ≫ coneDesc0 a b f g = f := by
  unfold coneIL coneDesc0
  rw [Category.assoc, inrX_zero_comp_XIso_assoc, ← Category.assoc, inl_f_biprodXIso_hom]
  simp

open HomologicalComplex in
theorem coneIP_desc0 {Z : Rep.{0} ℚ Γ} (f : L.X 0 ⟶ Z) (g : P.X 0 ⟶ Z) :
    coneIP a b 0 ≫ coneDesc0 a b f g = g := by
  unfold coneIP coneDesc0
  rw [Category.assoc, inrX_zero_comp_XIso_assoc, ← Category.assoc, inr_f_biprodXIso_hom]
  simp

open HomologicalComplex in
theorem coneExt0 {Z : Rep.{0} ℚ Γ} {f g : (pushCone a b).X 0 ⟶ Z} (hL : coneIL a b 0 ≫ f = coneIL a b 0 ≫ g)
    (hP : coneIP a b 0 ≫ f = coneIP a b 0 ≫ g) : f = g := by
  refine homotopyCofiber.ext_from_X' (pushArrow a b) 0 down_not_rel_zero ?_
  apply biprodX_ext_from
  · simpa [coneIL, Category.assoc] using hL
  · simpa [coneIP, Category.assoc] using hP

open HomologicalComplex in
theorem coneExt (n : ℕ) {Z : Rep.{0} ℚ Γ} {f g : (pushCone a b).X (n+1) ⟶ Z}
    (hA : coneIA a b n ≫ f = coneIA a b n ≫ g) (hL : coneIL a b (n+1) ≫ f = coneIL a b (n+1) ≫ g)
    (hP : coneIP a b (n+1) ≫ f = coneIP a b (n+1) ≫ g) : f = g := by
  refine homotopyCofiber.ext_from_X (pushArrow a b) n (n+1) (down_rel_succ n) ?_ ?_
  · exact hA
  · apply biprodX_ext_from
    · simpa [coneIL, Category.assoc] using hL
    · simpa [coneIP, Category.assoc] using hP

open HomologicalComplex in
theorem coneDL (n : ℕ) :
    coneIL a b (n+1) ≫ (pushCone a b).d (n+1) n = L.d (n+1) n ≫ coneIL a b n := by
  unfold coneIL
  rw [Category.assoc]
  change _ ≫ homotopyCofiber.inrX (pushArrow a b) (n+1) ≫ homotopyCofiber.d (pushArrow a b) (n+1) n = _
  rw [homotopyCofiber.inrX_d, ← Category.assoc, ← Category.assoc]
  congr 1
  exact ((biprod.inl : L ⟶ L ⊞ P).comm (n+1) n)

open HomologicalComplex in
theorem coneDP (n : ℕ) :
    coneIP a b (n+1) ≫ (pushCone a b).d (n+1) n = P.d (n+1) n ≫ coneIP a b n := by
  unfold coneIP
  rw [Category.assoc]
  change _ ≫ homotopyCofiber.inrX (pushArrow a b) (n+1) ≫ homotopyCofiber.d (pushArrow a b) (n+1) n = _
  rw [homotopyCofiber.inrX_d, ← Category.assoc, ← Category.assoc]
  congr 1
  exact ((biprod.inr : P ⟶ L ⊞ P).comm (n+1) n)

open HomologicalComplex in
theorem coneDA0 :
    coneIA a b 0 ≫ (pushCone a b).d 1 0 = a.f 0 ≫ coneIL a b 0 - b.f 0 ≫ coneIP a b 0 := by
  unfold coneIA coneIL coneIP
  change homotopyCofiber.inlX (pushArrow a b) 0 1 (down_rel_succ 0) ≫ homotopyCofiber.d (pushArrow a b) 1 0 = _
  rw [homotopyCofiber.inlX_d' (pushArrow a b) 1 0 (down_rel_succ 0) down_not_rel_zero, pushArrow_f]
  simp only [Preadditive.sub_comp, Category.assoc]

open HomologicalComplex in
theorem coneDA (n : ℕ) :
    coneIA a b (n+1) ≫ (pushCone a b).d (n+2) (n+1) =
      -(A.d (n+1) n ≫ coneIA a b n) + a.f (n+1) ≫ coneIL a b (n+1) - b.f (n+1) ≫ coneIP a b (n+1) := by
  unfold coneIA coneIL coneIP
  change homotopyCofiber.inlX (pushArrow a b) (n+1) (n+2) (down_rel_succ (n+1)) ≫
    homotopyCofiber.d (pushArrow a b) (n+2) (n+1) = _
  rw [homotopyCofiber.inlX_d (pushArrow a b) (n+2) (n+1) n (down_rel_succ (n+1)) (down_rel_succ n),
    pushArrow_f]
  simp only [Preadditive.sub_comp, Category.assoc]
  abel

/-- Mathlib's homotopy cofiber of the signed arrow has the coordinate presentation `PushCone`. -/
def pushConeOfCofiber : PushCone A L P (pushCone a b) a b where
  iA := coneIA a b
  iL := coneIL a b
  iP := coneIP a b
  desc0 := coneDesc0 a b
  desc := coneDesc a b
  iL0_desc0 := coneIL_desc0 a b
  iP0_desc0 := coneIP_desc0 a b
  ext0 := coneExt0 a b
  iA_desc := coneIA_desc a b
  iL_desc := coneIL_desc a b
  iP_desc := coneIP_desc a b
  ext := coneExt a b
  dL := coneDL a b
  dP := coneDP a b
  dA0 := coneDA0 a b
  dA := coneDA a b

end Cofiber

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
