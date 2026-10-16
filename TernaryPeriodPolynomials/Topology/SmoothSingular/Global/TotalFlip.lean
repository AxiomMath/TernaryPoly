module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.TotalComparison

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Limits

variable (K : RealBicomplex)

/-- Switching the actual bicomplex axes reverses the degree-one diagonal. -/
def totalFlipOne : TotalOne K ≃ₗ[ℝ] TotalOne K.flip := LinearEquiv.prodComm ℝ _ _

/-- Switching axes in degree two includes the genuine Koszul sign in bidegree (1,1). -/
def totalFlipTwo : TotalTwo K ≃ₗ[ℝ] TotalTwo K.flip where
  toFun x := (x.2.2,-x.2.1,x.1)
  invFun x := (x.2.2,-x.2.1,x.1)
  left_inv x := Prod.ext rfl (Prod.ext (neg_neg x.2.1) rfl)
  right_inv x := Prod.ext rfl (Prod.ext (neg_neg x.2.1) rfl)
  map_add' x y := Prod.ext rfl (Prod.ext (neg_add x.2.1 y.2.1) rfl)
  map_smul' c x := Prod.ext rfl (Prod.ext (smul_neg c x.2.1).symm rfl)

/-- Switching axes reverses the degree-three diagonal; all its Koszul signs are positive. -/
def totalFlipThree : TotalThree K ≃ₗ[ℝ] TotalThree K.flip where
  toFun x := (x.2.2.2,x.2.2.1,x.2.1,x.1)
  invFun x := (x.2.2.2,x.2.2.1,x.2.1,x.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The degree-one flip commutes with the actual signed total differential. -/
theorem totalFlipOne_d (x : TotalOne K) :
    totalOneD K.flip (totalFlipOne K x) = totalFlipTwo K (totalOneD K x) := by
  rcases x with ⟨a,b⟩
  apply Prod.ext
  · rfl
  apply Prod.ext
  · change -horizontal K 0 1 b + vertical K 1 0 a =
      -(-vertical K 1 0 a + horizontal K 0 1 b)
    abel
  · rfl

/-- The degree-two flip commutes with the actual signed total differential. -/
theorem totalFlipTwo_d (x : TotalTwo K) :
    totalTwoD K.flip (totalFlipTwo K x) = totalFlipThree K (totalTwoD K x) := by
  rcases x with ⟨a,b,c⟩
  apply Prod.ext
  · rfl
  apply Prod.ext
  · change horizontal K 0 2 c + vertical K 1 1 (-b) =
      -vertical K 1 1 b + horizontal K 0 2 c
    rw [map_neg]
    exact add_comm _ _
  apply Prod.ext
  · change -horizontal K 1 1 (-b) + vertical K 2 0 a =
      vertical K 2 0 a + horizontal K 1 1 b
    rw [map_neg, neg_neg]
    exact add_comm _ _
  · rfl

/-- The actual signed total window is canonically isomorphic to that of the flipped bicomplex. -/
def totalFlipIso : totalWindow K ≅ totalWindow K.flip :=
  ShortComplex.isoMk (totalFlipOne K).toModuleIso (totalFlipTwo K).toModuleIso
    (totalFlipThree K).toModuleIso
    (ModuleCat.hom_ext (LinearMap.ext (totalFlipOne_d K)))
    (ModuleCat.hom_ext (LinearMap.ext (totalFlipTwo_d K)))

/-- The actual homology isomorphism that permits a column-exact finite staircase. -/
def totalFlipHomologyIso : (totalWindow K).homology ≅ (totalWindow K.flip).homology :=
  ShortComplex.homologyMapIso (totalFlipIso K)

end TernaryPoly.SmoothSingularGlobal
