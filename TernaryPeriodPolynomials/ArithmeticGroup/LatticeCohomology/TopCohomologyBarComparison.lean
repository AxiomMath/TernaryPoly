module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCohomology.TopCohomologyQuotient
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Batteries.Data.List.Count
public import Mathlib.Algebra.Group.Subgroup.Finsupp
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.Group.TypeTags.Pointwise
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.RingTheory.SimpleRing.Matrix

@[expose] public section


open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section
namespace TernaryPoly.LatticeTopCohomology

abbrev Bar := Rep.barResolution ℚ Lattice
abbrev B (n : ℕ) := Rep.free ℚ Lattice (Fin n → Lattice)
abbrev barGen {n : ℕ} (g : Fin n → Lattice) : B n :=
  Finsupp.single g (MonoidAlgebra.single 1 1)

def toBar₀ : P₀ ⟶ B 0 := Rep.leftRegularHom _ (barGen ![])
def toBar₁ : P₁ ⟶ B 1 :=
  Rep.freeLift ℚ Lattice _ (fun i => barGen ![![first,second] i])
def toBar₂ : P₂ ⟶ B 2 :=
  Rep.leftRegularHom _ (barGen ![first,second] - barGen ![second,first])

@[simp] theorem toBar₀_single (g : Lattice) (r : ℚ) :
    toBar₀.hom (MonoidAlgebra.single g r) =
      Finsupp.single ![] (MonoidAlgebra.single g r) := by
  simp [toBar₀, barGen, Representation.finsupp_single, Representation.ofMulAction_single]

@[simp] theorem toBar₁_single (i : Fin 2) (g : Lattice) (r : ℚ) :
    toBar₁.hom (Finsupp.single i (MonoidAlgebra.single g r)) =
      Finsupp.single ![![first,second] i] (MonoidAlgebra.single g r) := by
  simp [toBar₁, barGen, Representation.finsupp_single, Representation.ofMulAction_single]

@[simp] theorem toBar₂_one : toBar₂.hom (MonoidAlgebra.single 1 1) =
    barGen ![first,second] - barGen ![second,first] := by simp [toBar₂]

theorem bar_d₀ (g : Lattice) : (Rep.barComplex.d ℚ Lattice 0).hom (barGen ![g]) =
    Finsupp.single ![] (MonoidAlgebra.single g 1) - barGen ![] := by
  rw [Rep.barComplex.d_single]
  have h₁ : (fun i : Fin 0 => (![g] : Fin 1 → Lattice) i.succ) = ![] := by funext i; exact i.elim0
  have h₂ : Fin.contractNth 0 (· * ·) (![g] : Fin 1 → Lattice) = ![] := by funext i; exact i.elim0
  rw [h₁]
  simp [h₂,barGen,sub_eq_add_neg]

theorem bar_d₁ (g h : Lattice) : (Rep.barComplex.d ℚ Lattice 1).hom (barGen ![g,h]) =
    Finsupp.single ![h] (MonoidAlgebra.single g 1) - barGen ![g*h] + barGen ![g] := by
  rw [Rep.barComplex.d_single]
  have h₁ : (fun i : Fin 1 => (![g,h] : Fin 2 → Lattice) i.succ) = ![h] := by funext i; fin_cases i; rfl
  have h₂ : Fin.contractNth 0 (· * ·) (![g,h] : Fin 2 → Lattice) = ![g*h] := by
    funext i; fin_cases i; rfl
  have h₃ : Fin.contractNth 1 (· * ·) (![g,h] : Fin 2 → Lattice) = ![g] := by
    funext i; fin_cases i; rfl
  rw [h₁]
  simp [Fin.sum_univ_succ,h₂,h₃,barGen,sub_eq_add_neg,add_assoc]

theorem toBar₁_comm : toBar₁ ≫ Bar.complex.d 1 0 = d₁ ≫ toBar₀ := by
  apply Rep.free_ext ℚ Lattice
  intro i
  change (Rep.barComplex.d ℚ Lattice 0).hom
    (toBar₁.hom (Finsupp.single i (MonoidAlgebra.single 1 1))) =
    toBar₀.hom (d₁.hom (Finsupp.single i (MonoidAlgebra.single 1 1)))
  rw [toBar₁_single, d₁_single, one_smul, one_mul, map_sub, toBar₀_single, toBar₀_single]
  exact bar_d₀ _

theorem toBar₂_comm : toBar₂ ≫ Bar.complex.d 2 1 = d₂ ≫ toBar₁ := by
  apply (Rep.leftRegularHomEquiv _).injective
  change (Rep.barComplex.d ℚ Lattice 1).hom
    (toBar₂.hom (MonoidAlgebra.single 1 1)) =
    toBar₁.hom (d₂.hom (MonoidAlgebra.single 1 1))
  rw [toBar₂_one, map_sub, bar_d₁, bar_d₁, d₂_single]
  simp only [one_smul, one_mul, map_sub, map_add]
  rw [toBar₁_single 0 1 1, toBar₁_single 1 first 1,
    toBar₁_single 0 second 1, toBar₁_single 1 1 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [mul_comm second first]
  dsimp [barGen]
  abel

def toBarComponents : (n : ℕ) → complex.X n ⟶ Bar.complex.X n
  | 0 => toBar₀
  | 1 => toBar₁
  | 2 => toBar₂
  | _ + 3 => 0

/-- The oriented grid maps into the actual bar resolution by antisymmetrizing each square. -/
def toBar : complex ⟶ Bar.complex where
  f := toBarComponents
  comm' i j hij := by
    have h : j+1=i := hij
    subst i
    rcases j with _ | _ | j
    · exact toBar₁_comm
    · exact toBar₂_comm
    · simp [toBarComponents, complex, differential]
      exact zero_comp

theorem diagonalSucc_inv_single (n : ℕ) (f : Fin n → Lattice) (g : Lattice) (r : ℚ) :
    (Rep.diagonalSuccIsoFree ℚ Lattice n).inv.hom
      (Finsupp.single f (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by
  simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial, Iso.trans_inv,
    Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have step : (Rep.Hom.hom (Rep.leftRegularTensorTrivialIsoFree ℚ Lattice (Fin n → Lattice)).inv)
      (Finsupp.single f (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single g 1 ⊗ₜ[ℚ] MonoidAlgebra.single f r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
  rw [step]
  simp only [Action.tensorObj_V, Rep.tensor_V, Rep.tensor_ρ]
  have key₁ := Representation.linearizeMap_single (k := ℚ)
    (Action.diagonalSuccIsoTensorTrivial Lattice n).inv (g, f) ((1 : ℚ) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := ℚ)
    (X := Action.leftRegular Lattice) (Y := Action.trivial Lattice (Fin n → Lattice)) g f 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial Lattice n).inv) z) key₂).trans key₁).trans (by
      simp only [one_mul]
      exact congrArg (fun x => MonoidAlgebra.single x r)
        (Action.diagonalSuccIsoTensorTrivial_inv_hom_apply g f))

theorem toBar_augmentation : toBar ≫ Bar.π = augmentation := by
  apply (complex.toSingle₀Equiv Trivial).injective
  apply Subtype.ext
  change toBar₀ ≫ Bar.π.f 0 = augmentationHom
  apply (Rep.leftRegularHomEquiv Trivial).injective
  change (Bar.π.f 0).hom (toBar₀.hom (MonoidAlgebra.single 1 1)) =
    augmentationHom.hom (MonoidAlgebra.single 1 1)
  rw [augmentationHom_single, toBar₀_single]
  change (Rep.standardComplex.ε ℚ Lattice).hom
    ((Rep.diagonalSuccIsoFree ℚ Lattice 0).inv.hom (barGen ![])) = 1
  rw [diagonalSucc_inv_single]
  simp [Rep.standardComplex.ε]

/-- The explicit oriented grid comparison is a genuine homotopy equivalence. -/
def toBarHomotopyEquiv : HomotopyEquiv complex Bar.complex :=
  (resolution.homotopyEquiv Bar).copy (ProjectiveResolution.liftHomotopy (𝟙 Trivial)
    _ toBar (by simp [ProjectiveResolution.homotopyEquiv]) (by simpa [resolution] using toBar_augmentation))

variable (A : Rep ℚ Lattice)

def homPullback {P Q : ChainComplex (Rep ℚ Lattice) ℕ} (f : P ⟶ Q) :
    Q.linearYonedaObj ℚ A ⟶ P.linearYonedaObj ℚ A :=
  (HomologicalComplex.unopFunctor (ModuleCat ℚ) (ComplexShape.down ℕ)).map
    ((((linearYoneda ℚ (Rep ℚ Lattice)).obj A).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map f).op

def homPullbackEquiv {P Q : ChainComplex (Rep ℚ Lattice) ℕ} (h : HomotopyEquiv P Q) :
    HomotopyEquiv (Q.linearYonedaObj ℚ A) (P.linearYonedaObj ℚ A) where
  hom := homPullback A h.hom
  inv := homPullback A h.inv
  homotopyHomInvId := by
    exact (((linearYoneda ℚ (Rep ℚ Lattice)).obj A).rightOp.mapHomotopy h.homotopyInvHomId).unop
  homotopyInvHomId := by
    exact (((linearYoneda ℚ (Rep ℚ Lattice)).obj A).rightOp.mapHomotopy h.homotopyHomInvId).unop

/-- A concrete comparison from actual inhomogeneous cochains to the lattice resolution. -/
def cochainsComparison : HomotopyEquiv (groupCohomology.inhomogeneousCochains A) (homComplex A) :=
  (HomotopyEquiv.ofIso (groupCohomology.inhomogeneousCochainsIso A)).trans
    (homPullbackEquiv A toBarHomotopyEquiv)

theorem cochainsComparison_one (f : (Fin 1 → Lattice) → A) (i : Fin 2) :
    edgeCoordinate A ((cochainsComparison A).hom.f 1 f) i = f ![![first,second] i] := by
  change (Rep.freeLift ℚ Lattice A f).hom
    (toBar₁.hom (Finsupp.single i (MonoidAlgebra.single 1 1))) = _
  rw [toBar₁_single]
  simp [Rep.freeLift]

theorem cochainsComparison_two (f : (Fin 2 → Lattice) → A) :
    topCoordinate A ((cochainsComparison A).hom.f 2 f) = f ![first,second] - f ![second,first] := by
  change (Rep.freeLift ℚ Lattice A f).hom (toBar₂.hom (MonoidAlgebra.single 1 1)) = _
  rw [toBar₂_one, map_sub]
  simp [barGen, Rep.freeLift]

end TernaryPoly.LatticeTopCohomology
