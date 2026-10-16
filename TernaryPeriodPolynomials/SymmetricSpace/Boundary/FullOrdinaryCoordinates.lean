module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullConeCoordinates
public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.FullBarCoordinates
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Boundary.OrdinaryBoundaryConeConsumer

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryFull
open CategoryTheory HomologicalComplex EquivariantSingularSmall OrdinaryParabolicGroups groupCohomology

/-- Reorder corner-line-plane to plane-line-corner, negating the corner exactly once. -/
def ordinaryReorder (A C D : Type) [AddCommGroup A] [Module ℚ A]
    [AddCommGroup C] [Module ℚ C] [AddCommGroup D] [Module ℚ D] :
    (A × C × D) ≃ₗ[ℚ] (D × C × A) where
  toFun x := (x.2.2,x.2.1,-x.1)
  invFun x := (-x.2.2,x.2.1,x.1)
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp only [Prod.fst_add,Prod.snd_add,neg_add]; rfl
  map_smul' r x := by
    change (r • x.2.2,r • x.2.1,-(r • x.1)) = (r • x.2.2,r • x.2.1,r • (-x.1))
    rw [smul_neg]

variable (W : Rep.{0} ℚ ModThreeGoodAction.IntegralGL)

def ordinaryCoordinates0 : (canonicalFaceCone.X 0 ⟶ W) ≃ₗ[ℚ] OrdinaryBoundaryCone.C0 W :=
  (signedConeHomZero canonicalLineArrow canonicalPlaneArrow W).trans
    ((LinearEquiv.prodCongr (inducedCoordinates0 Q W) (inducedCoordinates0 P W)).trans
      (LinearEquiv.prodComm ℚ W W))

def ordinaryCoordinates1 : (canonicalFaceCone.X 1 ⟶ W) ≃ₗ[ℚ] OrdinaryBoundaryCone.C1 W P Q :=
  (signedConeHomSucc canonicalLineArrow canonicalPlaneArrow W 0).trans
    ((LinearEquiv.prodCongr (inducedCoordinates0 B W)
      (LinearEquiv.prodCongr (inducedCoordinates1 Q W) (inducedCoordinates1 P W))).trans
        (ordinaryReorder W (Q → W) (P → W)))

def ordinaryCoordinates2 : (canonicalFaceCone.X 2 ⟶ W) ≃ₗ[ℚ] OrdinaryBoundaryCone.C2 W P Q :=
  (signedConeHomSucc canonicalLineArrow canonicalPlaneArrow W 1).trans
    ((LinearEquiv.prodCongr (inducedCoordinates1 B W)
      (LinearEquiv.prodCongr (inducedCoordinates2 Q W) (inducedCoordinates2 P W))).trans
        (ordinaryReorder (B → W) (Q × Q → W) (P × P → W)))

def canonicalLineInclusion (n : ℕ) : (inducedBarComplex Q).X n ⟶ canonicalFaceCone.X n :=
  signedLineInclusion canonicalLineArrow canonicalPlaneArrow n

def canonicalPlaneInclusion (n : ℕ) : (inducedBarComplex P).X n ⟶ canonicalFaceCone.X n :=
  signedPlaneInclusion canonicalLineArrow canonicalPlaneArrow n

def canonicalCornerInclusion (n : ℕ) : (inducedBarComplex B).X n ⟶ canonicalFaceCone.X (n+1) :=
  signedCornerInclusion canonicalLineArrow canonicalPlaneArrow n

def canonicalLineCochain (n : ℕ) (c : canonicalFaceCone.X n ⟶ W) : (inducedBarComplex Q).X n ⟶ W :=
  canonicalLineInclusion n ≫ c

def canonicalPlaneCochain (n : ℕ) (c : canonicalFaceCone.X n ⟶ W) : (inducedBarComplex P).X n ⟶ W :=
  canonicalPlaneInclusion n ≫ c

def canonicalCornerCochain (n : ℕ) (c : canonicalFaceCone.X (n+1) ⟶ W) : (inducedBarComplex B).X n ⟶ W :=
  canonicalCornerInclusion n ≫ c

theorem ordinaryCoordinates0_apply (c : canonicalFaceCone.X 0 ⟶ W) :
    ordinaryCoordinates0 W c = (inducedCoordinates0 P W (canonicalPlaneCochain W 0 c),
      inducedCoordinates0 Q W (canonicalLineCochain W 0 c)) := by
  have h := signedConeHomZero_apply canonicalLineArrow canonicalPlaneArrow W c
  exact congrArg (fun x => (inducedCoordinates0 P W x.2,inducedCoordinates0 Q W x.1)) h

theorem ordinaryCoordinates1_apply (c : canonicalFaceCone.X 1 ⟶ W) :
    ordinaryCoordinates1 W c = (inducedCoordinates1 P W (canonicalPlaneCochain W 1 c),
      inducedCoordinates1 Q W (canonicalLineCochain W 1 c),
      -inducedCoordinates0 B W (canonicalCornerCochain W 0 c)) := by
  have h := signedConeHomSucc_apply canonicalLineArrow canonicalPlaneArrow W 0 c
  unfold ordinaryCoordinates1
  change (inducedCoordinates1 P W ((signedConeHomSucc canonicalLineArrow canonicalPlaneArrow W 0 c).2.2),
    inducedCoordinates1 Q W ((signedConeHomSucc canonicalLineArrow canonicalPlaneArrow W 0 c).2.1),
    -inducedCoordinates0 B W ((signedConeHomSucc canonicalLineArrow canonicalPlaneArrow W 0 c).1)) = _
  rw [h]
  rfl

theorem ordinaryCoordinates2_apply (c : canonicalFaceCone.X 2 ⟶ W) :
    ordinaryCoordinates2 W c = (inducedCoordinates2 P W (canonicalPlaneCochain W 2 c),
      inducedCoordinates2 Q W (canonicalLineCochain W 2 c),
      -inducedCoordinates1 B W (canonicalCornerCochain W 1 c)) := by
  have h := signedConeHomSucc_apply canonicalLineArrow canonicalPlaneArrow W 1 c
  unfold ordinaryCoordinates2
  change (inducedCoordinates2 P W ((signedConeHomSucc canonicalLineArrow canonicalPlaneArrow W 1 c).2.2),
    inducedCoordinates2 Q W ((signedConeHomSucc canonicalLineArrow canonicalPlaneArrow W 1 c).2.1),
    -inducedCoordinates1 B W ((signedConeHomSucc canonicalLineArrow canonicalPlaneArrow W 1 c).1)) = _
  rw [h]
  rfl

/-- Extracting the actual face cochain commutes with its induced bar differential. -/
theorem canonicalLineCochain_d (i j : ℕ) (c : canonicalFaceCone.X j ⟶ W) :
    canonicalLineCochain W i (canonicalFaceCone.d i j ≫ c) =
    (inducedBarComplex Q).d i j ≫ canonicalLineCochain W j c :=
  (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ c)
    (signedLineInclusion_d canonicalLineArrow canonicalPlaneArrow i j)).trans (Category.assoc _ _ _))

theorem canonicalPlaneCochain_d (i j : ℕ) (c : canonicalFaceCone.X j ⟶ W) :
    canonicalPlaneCochain W i (canonicalFaceCone.d i j ≫ c) =
    (inducedBarComplex P).d i j ≫ canonicalPlaneCochain W j c :=
  (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ c)
    (signedPlaneInclusion_d canonicalLineArrow canonicalPlaneArrow i j)).trans (Category.assoc _ _ _))

theorem canonicalCornerCochain_d0 (c : canonicalFaceCone.X 0 ⟶ W) :
    canonicalCornerCochain W 0 (canonicalFaceCone.d 1 0 ≫ c) =
    canonicalLineArrow.f 0 ≫ canonicalLineCochain W 0 c -
      canonicalPlaneArrow.f 0 ≫ canonicalPlaneCochain W 0 c := by
  have h : canonicalCornerInclusion 0 ≫ canonicalFaceCone.d 1 0 =
      canonicalLineArrow.f 0 ≫ canonicalLineInclusion 0 -
      canonicalPlaneArrow.f 0 ≫ canonicalPlaneInclusion 0 :=
    signedCornerInclusion_d_zero canonicalLineArrow canonicalPlaneArrow
  refine (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ c) h).trans ?_)
  simp only [Preadditive.sub_comp,Category.assoc,canonicalLineCochain,canonicalPlaneCochain]

theorem canonicalCornerCochain_d1 (c : canonicalFaceCone.X 1 ⟶ W) :
    canonicalCornerCochain W 1 (canonicalFaceCone.d 2 1 ≫ c) =
    -((inducedBarComplex B).d 1 0 ≫ canonicalCornerCochain W 0 c) +
      (canonicalLineArrow.f 1 ≫ canonicalLineCochain W 1 c -
        canonicalPlaneArrow.f 1 ≫ canonicalPlaneCochain W 1 c) := by
  have h : canonicalCornerInclusion 1 ≫ canonicalFaceCone.d 2 1 =
      -(inducedBarComplex B).d 1 0 ≫ canonicalCornerInclusion 0 +
      (canonicalLineArrow.f 1 ≫ canonicalLineInclusion 1 -
      canonicalPlaneArrow.f 1 ≫ canonicalPlaneInclusion 1) :=
    signedCornerInclusion_d_succ canonicalLineArrow canonicalPlaneArrow 0
  refine (Category.assoc _ _ _).symm.trans ((congrArg (fun m => m ≫ c) h).trans ?_)
  simp only [Preadditive.add_comp,Preadditive.sub_comp,Preadditive.neg_comp,Category.assoc,
    canonicalLineCochain,canonicalPlaneCochain,canonicalCornerCochain]

end TernaryPoly.SymmetricSpaceBoundaryFull
