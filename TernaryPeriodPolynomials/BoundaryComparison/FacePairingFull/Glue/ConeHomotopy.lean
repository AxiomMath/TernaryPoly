module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeStrata

@[expose] public section


/-!
# Uniqueness of cone maps up to homotopy

Two chain maps `G1, G2` between pushout cones `K = cone(A -> L (+) P)`, `K' = cone(A' -> L' (+) P')` (coordinate
presentation `PushCone`) which map the `L`- and `P`-strata into the `L'`- and `P'`-strata (`StrataData`) are chain
homotopic as soon as their three stratum maps `A -> A'`, `L -> L'`, `P -> P'` are, provided the cells `A n` are
projective and `L'`, `P'` are exact in positive degrees (`cone_maps_homotopic`).  The extra freedom of a cone map over
given stratum maps is a primitive `theta` of the obstruction cocycles `ELd`, `EPd` in `Hom(A, L')`, `Hom(A, P')`
(`Ext^{-1} = 0`), constructed degree by degree (`exists_theta`) from the projectivity of `A` and the exactness of
`L'`, `P'`.  This is the cone-level form of the fact that a morphism of cone sequences over given outer maps is
unique up to homotopy when the connecting `Ext^{-1}` vanishes (used for the canonicity of the comparison `Psi`
of Lemma C.2).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Glue

open CapCompat

section Coord

variable {Γ : Type} [Group Γ] {A L P K : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}
  (𝒞 : PushCone A L P K a b)

@[reassoc (attr := simp)] theorem cone_iA_pA (n : ℕ) : 𝒞.iA n ≫ 𝒞.pA n = 𝟙 _ := 𝒞.iA_desc n _ _ _
@[reassoc (attr := simp)] theorem cone_iL_pA (n : ℕ) : 𝒞.iL (n + 1) ≫ 𝒞.pA n = 0 := 𝒞.iL_desc n _ _ _
@[reassoc (attr := simp)] theorem cone_iP_pA (n : ℕ) : 𝒞.iP (n + 1) ≫ 𝒞.pA n = 0 := 𝒞.iP_desc n _ _ _
@[reassoc (attr := simp)] theorem cone_iA_pL (n : ℕ) : 𝒞.iA n ≫ 𝒞.pL n = 0 := 𝒞.iA_desc n _ _ _
@[reassoc (attr := simp)] theorem cone_iL_pL (n : ℕ) : 𝒞.iL (n + 1) ≫ 𝒞.pL n = 𝟙 _ := 𝒞.iL_desc n _ _ _
@[reassoc (attr := simp)] theorem cone_iP_pL (n : ℕ) : 𝒞.iP (n + 1) ≫ 𝒞.pL n = 0 := 𝒞.iP_desc n _ _ _
@[reassoc (attr := simp)] theorem cone_iA_pP (n : ℕ) : 𝒞.iA n ≫ 𝒞.pP n = 0 := 𝒞.iA_desc n _ _ _
@[reassoc (attr := simp)] theorem cone_iL_pP (n : ℕ) : 𝒞.iL (n + 1) ≫ 𝒞.pP n = 0 := 𝒞.iL_desc n _ _ _
@[reassoc (attr := simp)] theorem cone_iP_pP (n : ℕ) : 𝒞.iP (n + 1) ≫ 𝒞.pP n = 𝟙 _ := 𝒞.iP_desc n _ _ _
@[reassoc (attr := simp)] theorem cone_iL_pL0 : 𝒞.iL 0 ≫ 𝒞.pL0 = 𝟙 _ := 𝒞.iL0_desc0 _ _
@[reassoc (attr := simp)] theorem cone_iP_pL0 : 𝒞.iP 0 ≫ 𝒞.pL0 = 0 := 𝒞.iP0_desc0 _ _
@[reassoc (attr := simp)] theorem cone_iL_pP0 : 𝒞.iL 0 ≫ 𝒞.pP0 = 0 := 𝒞.iL0_desc0 _ _
@[reassoc (attr := simp)] theorem cone_iP_pP0 : 𝒞.iP 0 ≫ 𝒞.pP0 = 𝟙 _ := 𝒞.iP0_desc0 _ _

theorem cone_sum_succ (n : ℕ) :
    𝟙 (K.X (n + 1)) = 𝒞.pA n ≫ 𝒞.iA n + 𝒞.pL n ≫ 𝒞.iL (n + 1) + 𝒞.pP n ≫ 𝒞.iP (n + 1) := by
  apply 𝒞.ext n <;> simp

theorem cone_sum_zero : 𝟙 (K.X 0) = 𝒞.pL0 ≫ 𝒞.iL 0 + 𝒞.pP0 ≫ 𝒞.iP 0 := by
  apply 𝒞.ext0 <;> simp

/-- Two morphisms into a positive-degree term of a pushout cone are equal when their three coordinates are. -/
theorem cone_ext_to_succ {n : ℕ} {X : Rep.{0} ℚ Γ} {f g : X ⟶ K.X (n + 1)}
    (hA : f ≫ 𝒞.pA n = g ≫ 𝒞.pA n) (hL : f ≫ 𝒞.pL n = g ≫ 𝒞.pL n) (hP : f ≫ 𝒞.pP n = g ≫ 𝒞.pP n) :
    f = g := by
  calc f = f ≫ 𝟙 _ := (Category.comp_id f).symm
    _ = g ≫ 𝟙 _ := by
      rw [cone_sum_succ 𝒞 n]
      simp only [Preadditive.comp_add, ← Category.assoc, hA, hL, hP]
    _ = g := Category.comp_id g

theorem cone_ext_to_zero {X : Rep.{0} ℚ Γ} {f g : X ⟶ K.X 0}
    (hL : f ≫ 𝒞.pL0 = g ≫ 𝒞.pL0) (hP : f ≫ 𝒞.pP0 = g ≫ 𝒞.pP0) : f = g := by
  calc f = f ≫ 𝟙 _ := (Category.comp_id f).symm
    _ = g ≫ 𝟙 _ := by
      rw [cone_sum_zero 𝒞]
      simp only [Preadditive.comp_add, ← Category.assoc, hL, hP]
    _ = g := Category.comp_id g


section Dcoord

theorem cone_dA_pL (n : ℕ) : 𝒞.iA (n + 1) ≫ K.d (n + 2) (n + 1) ≫ 𝒞.pL n = a.f (n + 1) := by
  rw [← Category.assoc, 𝒞.dA n]; simp
theorem cone_dA_pP (n : ℕ) : 𝒞.iA (n + 1) ≫ K.d (n + 2) (n + 1) ≫ 𝒞.pP n = -b.f (n + 1) := by
  rw [← Category.assoc, 𝒞.dA n]; simp
theorem cone_dA_pA (n : ℕ) : 𝒞.iA (n + 1) ≫ K.d (n + 2) (n + 1) ≫ 𝒞.pA n = -A.d (n + 1) n := by
  rw [← Category.assoc, 𝒞.dA n]; simp
theorem cone_dL_pL (n : ℕ) : 𝒞.iL (n + 2) ≫ K.d (n + 2) (n + 1) ≫ 𝒞.pL n = L.d (n + 2) (n + 1) := by
  rw [← Category.assoc, 𝒞.dL (n + 1)]; simp
theorem cone_dL_pA (n : ℕ) : 𝒞.iL (n + 2) ≫ K.d (n + 2) (n + 1) ≫ 𝒞.pA n = 0 := by
  rw [← Category.assoc, 𝒞.dL (n + 1)]; simp
theorem cone_dL_pP (n : ℕ) : 𝒞.iL (n + 2) ≫ K.d (n + 2) (n + 1) ≫ 𝒞.pP n = 0 := by
  rw [← Category.assoc, 𝒞.dL (n + 1)]; simp
theorem cone_dP_pP (n : ℕ) : 𝒞.iP (n + 2) ≫ K.d (n + 2) (n + 1) ≫ 𝒞.pP n = P.d (n + 2) (n + 1) := by
  rw [← Category.assoc, 𝒞.dP (n + 1)]; simp
theorem cone_dP_pA (n : ℕ) : 𝒞.iP (n + 2) ≫ K.d (n + 2) (n + 1) ≫ 𝒞.pA n = 0 := by
  rw [← Category.assoc, 𝒞.dP (n + 1)]; simp
theorem cone_dP_pL (n : ℕ) : 𝒞.iP (n + 2) ≫ K.d (n + 2) (n + 1) ≫ 𝒞.pL n = 0 := by
  rw [← Category.assoc, 𝒞.dP (n + 1)]; simp
theorem cone_dA0_pL0 : 𝒞.iA 0 ≫ K.d 1 0 ≫ 𝒞.pL0 = a.f 0 := by
  rw [← Category.assoc, 𝒞.dA0]; simp
theorem cone_dA0_pP0 : 𝒞.iA 0 ≫ K.d 1 0 ≫ 𝒞.pP0 = -b.f 0 := by
  rw [← Category.assoc, 𝒞.dA0]; simp
theorem cone_dL1_pL0 : 𝒞.iL 1 ≫ K.d 1 0 ≫ 𝒞.pL0 = L.d 1 0 := by
  rw [← Category.assoc, 𝒞.dL 0]; simp
theorem cone_dL1_pP0 : 𝒞.iL 1 ≫ K.d 1 0 ≫ 𝒞.pP0 = 0 := by
  rw [← Category.assoc, 𝒞.dL 0]; simp
theorem cone_dP1_pP0 : 𝒞.iP 1 ≫ K.d 1 0 ≫ 𝒞.pP0 = P.d 1 0 := by
  rw [← Category.assoc, 𝒞.dP 0]; simp
theorem cone_dP1_pL0 : 𝒞.iP 1 ≫ K.d 1 0 ≫ 𝒞.pL0 = 0 := by
  rw [← Category.assoc, 𝒞.dP 0]; simp

end Dcoord

end Coord

section Data

variable {Γ : Type} [Group Γ]
  {A L P K A' L' P' K' : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P} {a' : A' ⟶ L'} {b' : A' ⟶ P'}
  (𝒞 : PushCone A L P K a b) (𝒟 : PushCone A' L' P' K' a' b')

/-- The `L'`-coordinate of the image of the shifted corner coordinate. -/
def ThL (G : K ⟶ K') (n : ℕ) : A.X n ⟶ L'.X (n + 1) := 𝒞.iA n ≫ G.f (n + 1) ≫ 𝒟.pL n

/-- The `P'`-coordinate of the image of the shifted corner coordinate. -/
def ThP (G : K ⟶ K') (n : ℕ) : A.X n ⟶ P'.X (n + 1) := 𝒞.iA n ≫ G.f (n + 1) ≫ 𝒟.pP n

/-- A chain map of pushout cones preserving the `L`- and `P`-coordinates, with its three strata maps. -/
structure StrataData (G : K ⟶ K') where
  lA : A ⟶ A'
  lL : L ⟶ L'
  lP : P ⟶ P'
  hL : ∀ n, 𝒞.iL n ≫ G.f n = lL.f n ≫ 𝒟.iL n
  hP : ∀ n, 𝒞.iP n ≫ G.f n = lP.f n ≫ 𝒟.iP n
  hA : ∀ n, 𝒞.iA n ≫ G.f (n + 1) ≫ 𝒟.pA n = lA.f n

variable {𝒞 𝒟} {G : K ⟶ K'} (D : StrataData 𝒞 𝒟 G)

theorem StrataData.iA_G (n : ℕ) :
    𝒞.iA n ≫ G.f (n + 1) = D.lA.f n ≫ 𝒟.iA n + ThL 𝒞 𝒟 G n ≫ 𝒟.iL (n + 1) +
      ThP 𝒞 𝒟 G n ≫ 𝒟.iP (n + 1) := by
  calc 𝒞.iA n ≫ G.f (n + 1) = (𝒞.iA n ≫ G.f (n + 1)) ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = _ := by
      rw [cone_sum_succ 𝒟 n]
      simp only [Preadditive.comp_add, ThL, ThP, ← D.hA n, Category.assoc]

theorem StrataData.iL_G (n : ℕ) : 𝒞.iL (n + 1) ≫ G.f (n + 1) = D.lL.f (n + 1) ≫ 𝒟.iL (n + 1) := D.hL _
theorem StrataData.iP_G (n : ℕ) : 𝒞.iP (n + 1) ≫ G.f (n + 1) = D.lP.f (n + 1) ≫ 𝒟.iP (n + 1) := D.hP _

theorem StrataData.relL (n : ℕ) :
    ThL 𝒞 𝒟 G (n + 1) ≫ L'.d (n + 2) (n + 1) + D.lA.f (n + 1) ≫ a'.f (n + 1) =
      -(A.d (n + 1) n ≫ ThL 𝒞 𝒟 G n) + a.f (n + 1) ≫ D.lL.f (n + 1) := by
  have h1 : (𝒞.iA (n + 1) ≫ G.f (n + 2)) ≫ K'.d (n + 2) (n + 1) ≫ 𝒟.pL n =
      (𝒞.iA (n + 1) ≫ K.d (n + 2) (n + 1)) ≫ G.f (n + 1) ≫ 𝒟.pL n := by
    rw [Category.assoc, Category.assoc, ← Category.assoc (G.f (n + 2)), G.comm (n + 2) (n + 1),
      Category.assoc]
  have hl : 𝒞.iA (n + 1) ≫ G.f (n + 2) = D.lA.f (n + 1) ≫ 𝒟.iA (n + 1) + ThL 𝒞 𝒟 G (n + 1) ≫ 𝒟.iL (n + 2) +
      ThP 𝒞 𝒟 G (n + 1) ≫ 𝒟.iP (n + 2) := D.iA_G (n + 1)
  have hr : 𝒞.iA (n + 1) ≫ K.d (n + 2) (n + 1) = -(A.d (n + 1) n ≫ 𝒞.iA n) + a.f (n + 1) ≫ 𝒞.iL (n + 1) -
      b.f (n + 1) ≫ 𝒞.iP (n + 1) := 𝒞.dA n
  rw [hl, hr] at h1
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.neg_comp, Category.assoc,
    cone_dA_pL 𝒟, cone_dL_pL 𝒟, cone_dP_pL 𝒟] at h1
  have e1 : 𝒞.iL (n + 1) ≫ G.f (n + 1) ≫ 𝒟.pL n = D.lL.f (n + 1) := by
    rw [← Category.assoc, D.iL_G]; simp
  have e2 : 𝒞.iP (n + 1) ≫ G.f (n + 1) ≫ 𝒟.pL n = 0 := by
    rw [← Category.assoc, D.iP_G]; simp
  rw [e1, e2] at h1
  simp only [comp_zero, add_zero, sub_zero] at h1
  exact (add_comm _ _).trans (h1.trans (by simp [ThL]))

theorem StrataData.relP (n : ℕ) :
    ThP 𝒞 𝒟 G (n + 1) ≫ P'.d (n + 2) (n + 1) =
      D.lA.f (n + 1) ≫ b'.f (n + 1) + (-(A.d (n + 1) n ≫ ThP 𝒞 𝒟 G n) - b.f (n + 1) ≫ D.lP.f (n + 1)) := by
  have h1 : (𝒞.iA (n + 1) ≫ G.f (n + 2)) ≫ K'.d (n + 2) (n + 1) ≫ 𝒟.pP n =
      (𝒞.iA (n + 1) ≫ K.d (n + 2) (n + 1)) ≫ G.f (n + 1) ≫ 𝒟.pP n := by
    rw [Category.assoc, Category.assoc, ← Category.assoc (G.f (n + 2)), G.comm (n + 2) (n + 1),
      Category.assoc]
  have hl : 𝒞.iA (n + 1) ≫ G.f (n + 2) = D.lA.f (n + 1) ≫ 𝒟.iA (n + 1) + ThL 𝒞 𝒟 G (n + 1) ≫ 𝒟.iL (n + 2) +
      ThP 𝒞 𝒟 G (n + 1) ≫ 𝒟.iP (n + 2) := D.iA_G (n + 1)
  have hr : 𝒞.iA (n + 1) ≫ K.d (n + 2) (n + 1) = -(A.d (n + 1) n ≫ 𝒞.iA n) + a.f (n + 1) ≫ 𝒞.iL (n + 1) -
      b.f (n + 1) ≫ 𝒞.iP (n + 1) := 𝒞.dA n
  rw [hl, hr] at h1
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.neg_comp, Category.assoc,
    cone_dA_pP 𝒟, cone_dL_pP 𝒟, cone_dP_pP 𝒟] at h1
  have e1 : 𝒞.iL (n + 1) ≫ G.f (n + 1) ≫ 𝒟.pP n = 0 := by
    rw [← Category.assoc, D.iL_G]; simp
  have e2 : 𝒞.iP (n + 1) ≫ G.f (n + 1) ≫ 𝒟.pP n = D.lP.f (n + 1) := by
    rw [← Category.assoc, D.iP_G]; simp
  rw [e1, e2] at h1
  simp only [comp_zero, add_zero, Preadditive.comp_neg] at h1
  calc ThP 𝒞 𝒟 G (n + 1) ≫ P'.d (n + 2) (n + 1)
      = (-(D.lA.f (n + 1) ≫ b'.f (n + 1)) + ThP 𝒞 𝒟 G (n + 1) ≫ P'.d (n + 2) (n + 1)) +
        D.lA.f (n + 1) ≫ b'.f (n + 1) := by abel
    _ = (-(A.d (n + 1) n ≫ 𝒞.iA n ≫ G.f (n + 1) ≫ 𝒟.pP n) - b.f (n + 1) ≫ D.lP.f (n + 1)) +
        D.lA.f (n + 1) ≫ b'.f (n + 1) := by rw [h1]
    _ = _ := by simp only [ThP]; abel

theorem StrataData.relL0 :
    ThL 𝒞 𝒟 G 0 ≫ L'.d 1 0 + D.lA.f 0 ≫ a'.f 0 = a.f 0 ≫ D.lL.f 0 := by
  have h1 : (𝒞.iA 0 ≫ G.f 1) ≫ K'.d 1 0 ≫ 𝒟.pL0 = (𝒞.iA 0 ≫ K.d 1 0) ≫ G.f 0 ≫ 𝒟.pL0 := by
    rw [Category.assoc, Category.assoc, ← Category.assoc (G.f 1), G.comm 1 0, Category.assoc]
  have hl : 𝒞.iA 0 ≫ G.f 1 = D.lA.f 0 ≫ 𝒟.iA 0 + ThL 𝒞 𝒟 G 0 ≫ 𝒟.iL 1 + ThP 𝒞 𝒟 G 0 ≫ 𝒟.iP 1 := D.iA_G 0
  rw [hl, 𝒞.dA0] at h1
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.assoc, cone_dA0_pL0 𝒟, cone_dL1_pL0 𝒟,
    cone_dP1_pL0 𝒟] at h1
  have e1 : 𝒞.iL 0 ≫ G.f 0 ≫ 𝒟.pL0 = D.lL.f 0 := by
    rw [← Category.assoc, D.hL]; simp
  have e2 : 𝒞.iP 0 ≫ G.f 0 ≫ 𝒟.pL0 = 0 := by
    rw [← Category.assoc, D.hP]; simp
  rw [e1, e2] at h1
  simp only [comp_zero, add_zero, sub_zero] at h1
  exact (add_comm _ _).trans h1

theorem StrataData.relP0 :
    ThP 𝒞 𝒟 G 0 ≫ P'.d 1 0 = D.lA.f 0 ≫ b'.f 0 - b.f 0 ≫ D.lP.f 0 := by
  have h1 : (𝒞.iA 0 ≫ G.f 1) ≫ K'.d 1 0 ≫ 𝒟.pP0 = (𝒞.iA 0 ≫ K.d 1 0) ≫ G.f 0 ≫ 𝒟.pP0 := by
    rw [Category.assoc, Category.assoc, ← Category.assoc (G.f 1), G.comm 1 0, Category.assoc]
  have hl : 𝒞.iA 0 ≫ G.f 1 = D.lA.f 0 ≫ 𝒟.iA 0 + ThL 𝒞 𝒟 G 0 ≫ 𝒟.iL 1 + ThP 𝒞 𝒟 G 0 ≫ 𝒟.iP 1 := D.iA_G 0
  rw [hl, 𝒞.dA0] at h1
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.assoc, cone_dA0_pP0 𝒟, cone_dL1_pP0 𝒟,
    cone_dP1_pP0 𝒟] at h1
  have e1 : 𝒞.iL 0 ≫ G.f 0 ≫ 𝒟.pP0 = 0 := by
    rw [← Category.assoc, D.hL]; simp
  have e2 : 𝒞.iP 0 ≫ G.f 0 ≫ 𝒟.pP0 = D.lP.f 0 := by
    rw [← Category.assoc, D.hP]; simp
  rw [e1, e2] at h1
  simp only [comp_zero, add_zero, Preadditive.comp_neg] at h1
  calc ThP 𝒞 𝒟 G 0 ≫ P'.d 1 0
      = (-(D.lA.f 0 ≫ b'.f 0) + ThP 𝒞 𝒟 G 0 ≫ P'.d 1 0) + D.lA.f 0 ≫ b'.f 0 := by abel
    _ = (0 - b.f 0 ≫ D.lP.f 0) + D.lA.f 0 ≫ b'.f 0 := by rw [h1]
    _ = _ := by abel

end Data

section Theta

variable {Γ : Type} [Group Γ] (P N : ChainComplex (Rep.{0} ℚ Γ) ℕ) [∀ n, Projective (P.X n)]

/-- The state of the inductive construction of the primitives `θ`. -/
structure ThetaState (E : ∀ n, P.X n ⟶ N.X (n + 1)) (n : ℕ) where
  θ : P.X n ⟶ N.X (n + 2)
  R : P.X n ⟶ N.X (n + 1)
  hθ : θ ≫ N.d (n + 2) (n + 1) = R
  hI : P.d (n + 1) n ≫ R = P.d (n + 1) n ≫ E n

/-- **Primitives of an anticommuting family into an exact complex.**  If `N` is exact in positive degrees,
`P` consists of projectives, and `E n : P n ⟶ N (n+1)` anticommutes with the differentials
(`d E_{n+1} = - E_n d`, `d E_0 = 0`), there are `θ n : P n ⟶ N (n+2)` with
`θ_0 d = E_0` and `θ_{n+1} d = E_{n+1} + d_P θ_n`. -/
theorem exists_theta
    (hN : ∀ n, (ShortComplex.mk (N.d (n + 2) (n + 1)) (N.d (n + 1) n) (N.d_comp_d _ _ _)).Exact)
    (E : ∀ n, P.X n ⟶ N.X (n + 1)) (hE0 : E 0 ≫ N.d 1 0 = 0)
    (hE : ∀ n, E (n + 1) ≫ N.d (n + 2) (n + 1) = -(P.d (n + 1) n ≫ E n)) :
    ∃ θ : ∀ n, P.X n ⟶ N.X (n + 2), θ 0 ≫ N.d 2 1 = E 0 ∧
      ∀ n, θ (n + 1) ≫ N.d (n + 3) (n + 2) = E (n + 1) + P.d (n + 1) n ≫ θ n := by
  let s0 : ThetaState P N E 0 :=
    { θ := (hN 0).liftFromProjective (E 0) hE0
      R := E 0
      hθ := (hN 0).liftFromProjective_comp _ _
      hI := rfl }
  let step : ∀ n, ThetaState P N E n → ThetaState P N E (n + 1) := fun n s =>
    have hcyc : (E (n + 1) + P.d (n + 1) n ≫ s.θ) ≫ N.d (n + 2) (n + 1) = 0 := by
      rw [Preadditive.add_comp, Category.assoc, s.hθ, hE n, s.hI]
      simp
    { θ := (hN (n + 1)).liftFromProjective (E (n + 1) + P.d (n + 1) n ≫ s.θ) hcyc
      R := E (n + 1) + P.d (n + 1) n ≫ s.θ
      hθ := (hN (n + 1)).liftFromProjective_comp _ _
      hI := by
        rw [Preadditive.comp_add, ← Category.assoc, P.d_comp_d, zero_comp, add_zero] }
  let seq : ∀ n, ThetaState P N E n := fun n => Nat.rec s0 step n
  refine ⟨fun n => (seq n).θ, (seq 0).hθ, fun n => ?_⟩
  exact (seq (n + 1)).hθ

end Theta

section Hty

variable {Γ : Type} [Group Γ] {X Y : ChainComplex (Rep.{0} ℚ Γ) ℕ} {f g : X ⟶ Y} (s : Homotopy f g)

theorem hty_zero : f.f 0 = s.hom 0 1 ≫ Y.d 1 0 + g.f 0 := by
  have h := s.comm 0
  rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at h
  exact h

theorem hty_succ (n : ℕ) :
    f.f (n + 1) = X.d (n + 1) n ≫ s.hom n (n + 1) + s.hom (n + 1) (n + 2) ≫ Y.d (n + 2) (n + 1) + g.f (n + 1) := by
  have h := s.comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  exact h

end Hty

section EDef

variable {Γ : Type} [Group Γ]
  {A L P K A' L' P' K' : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P} {a' : A' ⟶ L'} {b' : A' ⟶ P'}
  {𝒞 : PushCone A L P K a b} {𝒟 : PushCone A' L' P' K' a' b'} {G1 G2 : K ⟶ K'}
  (D1 : StrataData 𝒞 𝒟 G1) (D2 : StrataData 𝒞 𝒟 G2)
  (sA : Homotopy D1.lA D2.lA) (sL : Homotopy D1.lL D2.lL) (sP : Homotopy D1.lP D2.lP)

/-- The obstruction cochain in the `L'`-coordinate. -/
def ELd (n : ℕ) : A.X n ⟶ L'.X (n + 1) :=
  (ThL 𝒞 𝒟 G1 n - ThL 𝒞 𝒟 G2 n) + sA.hom n (n + 1) ≫ a'.f (n + 1) - a.f n ≫ sL.hom n (n + 1)

/-- The obstruction cochain in the `P'`-coordinate. -/
def EPd (n : ℕ) : A.X n ⟶ P'.X (n + 1) :=
  (ThP 𝒞 𝒟 G1 n - ThP 𝒞 𝒟 G2 n) - sA.hom n (n + 1) ≫ b'.f (n + 1) + b.f n ≫ sP.hom n (n + 1)

theorem ELd_zero : ELd D1 D2 sA sL 0 ≫ L'.d 1 0 = 0 := by
  have t1 : ThL 𝒞 𝒟 G1 0 ≫ L'.d 1 0 = a.f 0 ≫ D1.lL.f 0 - D1.lA.f 0 ≫ a'.f 0 := eq_sub_of_add_eq D1.relL0
  have t2 : ThL 𝒞 𝒟 G2 0 ≫ L'.d 1 0 = a.f 0 ≫ D2.lL.f 0 - D2.lA.f 0 ≫ a'.f 0 := eq_sub_of_add_eq D2.relL0
  have hA := hty_zero sA
  have hL := hty_zero sL
  have hc : a'.f 1 ≫ L'.d 1 0 = A'.d 1 0 ≫ a'.f 0 := a'.comm 1 0
  unfold ELd
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.assoc, t1, t2, hc, hL, hA]
  simp only [Preadditive.comp_add]
  abel

theorem ELd_succ (n : ℕ) : ELd D1 D2 sA sL (n + 1) ≫ L'.d (n + 2) (n + 1) = -(A.d (n + 1) n ≫ ELd D1 D2 sA sL n) := by
  have t1 : ThL 𝒞 𝒟 G1 (n + 1) ≫ L'.d (n + 2) (n + 1) =
      -(A.d (n + 1) n ≫ ThL 𝒞 𝒟 G1 n) + a.f (n + 1) ≫ D1.lL.f (n + 1) - D1.lA.f (n + 1) ≫ a'.f (n + 1) := by
    rw [eq_sub_iff_add_eq]; exact D1.relL n
  have t2 : ThL 𝒞 𝒟 G2 (n + 1) ≫ L'.d (n + 2) (n + 1) =
      -(A.d (n + 1) n ≫ ThL 𝒞 𝒟 G2 n) + a.f (n + 1) ≫ D2.lL.f (n + 1) - D2.lA.f (n + 1) ≫ a'.f (n + 1) := by
    rw [eq_sub_iff_add_eq]; exact D2.relL n
  have hA := hty_succ sA n
  have hL := hty_succ sL n
  have hc : a'.f (n + 2) ≫ L'.d (n + 2) (n + 1) = A'.d (n + 2) (n + 1) ≫ a'.f (n + 1) := a'.comm (n + 2) (n + 1)
  have hac : A.d (n + 1) n ≫ a.f n = a.f (n + 1) ≫ L.d (n + 1) n := (a.comm (n + 1) n).symm
  have hac' : A.d (n + 1) n ≫ a.f n ≫ sL.hom n (n + 1) = a.f (n + 1) ≫ L.d (n + 1) n ≫ sL.hom n (n + 1) := by
    rw [← Category.assoc, hac, Category.assoc]
  unfold ELd
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.comp_add, Preadditive.comp_sub,
    Category.assoc, t1, t2, hc]
  rw [hA, hL]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, hac']
  abel

theorem EPd_zero : EPd D1 D2 sA sP 0 ≫ P'.d 1 0 = 0 := by
  have t1 : ThP 𝒞 𝒟 G1 0 ≫ P'.d 1 0 = D1.lA.f 0 ≫ b'.f 0 - b.f 0 ≫ D1.lP.f 0 := D1.relP0
  have t2 : ThP 𝒞 𝒟 G2 0 ≫ P'.d 1 0 = D2.lA.f 0 ≫ b'.f 0 - b.f 0 ≫ D2.lP.f 0 := D2.relP0
  have hA := hty_zero sA
  have hP := hty_zero sP
  have hc : b'.f 1 ≫ P'.d 1 0 = A'.d 1 0 ≫ b'.f 0 := b'.comm 1 0
  unfold EPd
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Category.assoc, t1, t2, hc, hP, hA]
  simp only [Preadditive.comp_add]
  abel

theorem EPd_succ (n : ℕ) : EPd D1 D2 sA sP (n + 1) ≫ P'.d (n + 2) (n + 1) = -(A.d (n + 1) n ≫ EPd D1 D2 sA sP n) := by
  have t1 := D1.relP n
  have t2 := D2.relP n
  have hA := hty_succ sA n
  have hP := hty_succ sP n
  have hc : b'.f (n + 2) ≫ P'.d (n + 2) (n + 1) = A'.d (n + 2) (n + 1) ≫ b'.f (n + 1) := b'.comm (n + 2) (n + 1)
  have hbc : A.d (n + 1) n ≫ b.f n = b.f (n + 1) ≫ P.d (n + 1) n := (b.comm (n + 1) n).symm
  have hbc' : A.d (n + 1) n ≫ b.f n ≫ sP.hom n (n + 1) = b.f (n + 1) ≫ P.d (n + 1) n ≫ sP.hom n (n + 1) := by
    rw [← Category.assoc, hbc, Category.assoc]
  unfold EPd
  simp only [Preadditive.add_comp, Preadditive.sub_comp, Preadditive.comp_add, Preadditive.comp_sub,
    Category.assoc, t1, t2, hc]
  rw [hA, hP]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, hbc']
  abel

include D1 D2 sA sL sP in
/-- **Uniqueness of cone maps up to homotopy.**  Two chain maps `G1, G2` between pushout cones, which map the
strata into the strata with homotopic stratum maps `lA, lL, lP`, are homotopic, provided the source cells `A n` are
projective and the target `L'`, `P'` are exact in positive degrees. -/
theorem cone_maps_homotopic [∀ n, Projective (A.X n)]
    (hexL : ∀ n, (ShortComplex.mk (L'.d (n + 2) (n + 1)) (L'.d (n + 1) n) (L'.d_comp_d _ _ _)).Exact)
    (hexP : ∀ n, (ShortComplex.mk (P'.d (n + 2) (n + 1)) (P'.d (n + 1) n) (P'.d_comp_d _ _ _)).Exact) :
    Nonempty (Homotopy G1 G2) := by
  obtain ⟨θL, hθL0, hθLs⟩ := exists_theta A L' hexL (ELd D1 D2 sA sL) (ELd_zero D1 D2 sA sL)
    (ELd_succ D1 D2 sA sL)
  obtain ⟨θP, hθP0, hθPs⟩ := exists_theta A P' hexP (EPd D1 D2 sA sP) (EPd_zero D1 D2 sA sP)
    (EPd_succ D1 D2 sA sP)
  let hL' : ∀ n, L.X n ⟶ K'.X (n + 1) := fun n => sL.hom n (n + 1) ≫ 𝒟.iL (n + 1)
  let hP' : ∀ n, P.X n ⟶ K'.X (n + 1) := fun n => sP.hom n (n + 1) ≫ 𝒟.iP (n + 1)
  let hA' : ∀ n, A.X n ⟶ K'.X (n + 2) := fun n =>
    -(sA.hom n (n + 1) ≫ 𝒟.iA (n + 1)) + θL n ≫ 𝒟.iL (n + 2) + θP n ≫ 𝒟.iP (n + 2)
  let hh : ∀ n, K.X n ⟶ K'.X (n + 1) := fun n => Nat.casesOn n (𝒞.desc0 (hL' 0) (hP' 0))
    (fun m => 𝒞.desc m (hA' m) (hL' (m + 1)) (hP' (m + 1)))
  have iL_hh : ∀ n, 𝒞.iL n ≫ hh n = hL' n := by
    intro n; cases n with
    | zero => exact 𝒞.iL0_desc0 _ _
    | succ m => exact 𝒞.iL_desc m _ _ _
  have iP_hh : ∀ n, 𝒞.iP n ≫ hh n = hP' n := by
    intro n; cases n with
    | zero => exact 𝒞.iP0_desc0 _ _
    | succ m => exact 𝒞.iP_desc m _ _ _
  have iA_hh : ∀ n, 𝒞.iA n ≫ hh (n + 1) = hA' n := fun n => 𝒞.iA_desc n _ _ _
  have hAd : ∀ n, hA' n ≫ K'.d (n + 2) (n + 1) =
      (sA.hom n (n + 1) ≫ A'.d (n + 1) n) ≫ 𝒟.iA n +
      (-(sA.hom n (n + 1) ≫ a'.f (n + 1)) + θL n ≫ L'.d (n + 2) (n + 1)) ≫ 𝒟.iL (n + 1) +
      (sA.hom n (n + 1) ≫ b'.f (n + 1) + θP n ≫ P'.d (n + 2) (n + 1)) ≫ 𝒟.iP (n + 1) := by
    intro n
    simp only [hA', Preadditive.add_comp, Preadditive.neg_comp, Category.assoc, 𝒟.dA n, 𝒟.dL (n + 1),
      𝒟.dP (n + 1), Preadditive.comp_add, Preadditive.comp_sub, Preadditive.comp_neg]
    abel
  have key0 : G1.f 0 = hh 0 ≫ K'.d 1 0 + G2.f 0 := by
    apply 𝒞.ext0
    · rw [Preadditive.comp_add, ← Category.assoc, iL_hh 0, D1.hL 0, D2.hL 0, hty_zero sL]
      simp only [hL', Category.assoc, 𝒟.dL 0, Preadditive.add_comp]
    · rw [Preadditive.comp_add, ← Category.assoc, iP_hh 0, D1.hP 0, D2.hP 0, hty_zero sP]
      simp only [hP', Category.assoc, 𝒟.dP 0, Preadditive.add_comp]
  have keyL : ∀ n, 𝒞.iL (n + 1) ≫ G1.f (n + 1) =
      𝒞.iL (n + 1) ≫ (K.d (n + 1) n ≫ hh n + hh (n + 1) ≫ K'.d (n + 2) (n + 1) + G2.f (n + 1)) := by
    intro n
    rw [Preadditive.comp_add, Preadditive.comp_add, ← Category.assoc (𝒞.iL (n + 1)) (K.d (n + 1) n),
      ← Category.assoc (𝒞.iL (n + 1)) (hh (n + 1)), D1.hL (n + 1), D2.hL (n + 1), 𝒞.dL n,
      Category.assoc, iL_hh n, iL_hh (n + 1), hty_succ sL n]
    simp only [hL', Category.assoc, 𝒟.dL (n + 1), Preadditive.add_comp]
  have keyP : ∀ n, 𝒞.iP (n + 1) ≫ G1.f (n + 1) =
      𝒞.iP (n + 1) ≫ (K.d (n + 1) n ≫ hh n + hh (n + 1) ≫ K'.d (n + 2) (n + 1) + G2.f (n + 1)) := by
    intro n
    rw [Preadditive.comp_add, Preadditive.comp_add, ← Category.assoc (𝒞.iP (n + 1)) (K.d (n + 1) n),
      ← Category.assoc (𝒞.iP (n + 1)) (hh (n + 1)), D1.hP (n + 1), D2.hP (n + 1), 𝒞.dP n,
      Category.assoc, iP_hh n, iP_hh (n + 1), hty_succ sP n]
    simp only [hP', Category.assoc, 𝒟.dP (n + 1), Preadditive.add_comp]
  have keyS : ∀ n, G1.f (n + 1) =
      K.d (n + 1) n ≫ hh n + hh (n + 1) ≫ K'.d (n + 2) (n + 1) + G2.f (n + 1) := by
    intro n
    apply 𝒞.ext n
    · rw [Preadditive.comp_add, Preadditive.comp_add, D1.iA_G n, D2.iA_G n,
        ← Category.assoc (𝒞.iA n) (hh (n + 1)), iA_hh n, hAd n]
      cases n with
      | zero =>
        rw [← Category.assoc (𝒞.iA 0) (K.d 1 0), 𝒞.dA0, Preadditive.sub_comp, Preadditive.add_comp,
          Category.assoc, Category.assoc, iL_hh 0, iP_hh 0]
        simp only [hL', hP', Category.assoc]
        refine cone_ext_to_succ 𝒟 ?_ ?_ ?_
        · simp
          exact hty_zero sA
        · simp
          rw [hθL0]; unfold ELd; abel
        · simp
          rw [hθP0]; unfold EPd; abel
      | succ m =>
        rw [← Category.assoc (𝒞.iA (m + 1)) (K.d (m + 1 + 1) (m + 1)), 𝒞.dA m, Preadditive.sub_comp,
          Preadditive.add_comp, Preadditive.neg_comp, Category.assoc, Category.assoc, Category.assoc,
          iA_hh m, iL_hh (m + 1), iP_hh (m + 1)]
        simp only [hL', hP', Category.assoc]
        refine cone_ext_to_succ 𝒟 ?_ ?_ ?_
        · simp [hA']
          rw [hty_succ sA m]
        · simp [hA']
          have h : θL (m + 1) ≫ L'.d (m + 1 + 2) (m + 1 + 1) =
              ELd D1 D2 sA sL (m + 1) + A.d (m + 1) m ≫ θL m := hθLs m
          rw [h]; unfold ELd; abel
        · simp [hA']
          have h : θP (m + 1) ≫ P'.d (m + 1 + 2) (m + 1 + 1) =
              EPd D1 D2 sA sP (m + 1) + A.d (m + 1) m ≫ θP m := hθPs m
          rw [h]; unfold EPd; abel
    · exact keyL n
    · exact keyP n
  refine ⟨{ hom := fun i j => if h : i + 1 = j then hh i ≫ eqToHom (by rw [h]) else 0
            zero := fun i j hij => dite_eq_right (fun h => hij (by rw [ComplexShape.down_Rel]; exact h))
            comm := fun i => ?_ }⟩
  cases i with
  | zero =>
    rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
    simpa using key0
  | succ n =>
    rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
    simpa using keyS n

end EDef

end TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
