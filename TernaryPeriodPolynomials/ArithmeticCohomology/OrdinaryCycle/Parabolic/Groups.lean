module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Parabolic.GroupsCoordinates

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryParabolicGroups
open ModThreeGoodAction RadicalFirstCohomologyLattice OrdinaryBoundaryCommonRoot
open RelativeStabilizerParameters PolynomialGLAction OrdinaryCovectors

/-- The exact 26-covector coefficient representation restricted to the full plane parabolic. -/
def planeParabolicCoefficients (n : ℕ) (e : ℤ) : Representation ℚ P (Coefficients n) :=
  (coefficientAction n e).comp P.subtype

/-- Pull back that actual representation along the literal semidirect multiplication map. -/
def planeCoefficients (n : ℕ) (e : ℤ) : Representation ℚ PlaneProduct (Coefficients n) :=
  (coefficientAction n e).comp planeLift

theorem planeCoefficients_pullback (n : ℕ) (e : ℤ) :
    planeCoefficients n e = (planeParabolicCoefficients n e).comp planeEquiv.toMonoidHom := rfl

@[simp] theorem planeCoefficients_inl (n : ℕ) (e : ℤ) (u : planeRadical) :
    planeCoefficients n e (SemidirectProduct.inl u) = coefficientAction n e u.val := by
  change coefficientAction n e (planeLift (SemidirectProduct.inl u)) = _
  simp [planeLift]

@[simp] theorem planeCoefficients_inr (n : ℕ) (e : ℤ) (q : PlaneLevi) :
    planeCoefficients n e (SemidirectProduct.inr q) = coefficientAction n e (planeLevi q) := by
  change coefficientAction n e (planeLift (SemidirectProduct.inr q)) = _
  simp [planeLift]

/-- Both the inverse polynomial action and the permutation of all 26 covectors are retained. -/
theorem planeCoefficients_radical_apply (n : ℕ) (e : ℤ) (u : planeRadical)
    (F : Coefficients n) (r : NonzeroCovector) :
    planeCoefficients n e (SemidirectProduct.inl u) F r =
      integralAction n e u.val (F (rowMove u.val r)) := by
  rw [planeCoefficients_inl]
  rfl

/-- The full independent-sign block matrix acts on the actual 26-covector coefficient system. -/
theorem planeCoefficients_levi_apply (n : ℕ) (e : ℤ) (q : PlaneLevi)
    (F : Coefficients n) (r : NonzeroCovector) :
    planeCoefficients n e (SemidirectProduct.inr q) F r =
      integralAction n e (planeElement q.1 0 q.2) (F (rowMove (planeElement q.1 0 q.2) r)) := by
  rw [planeCoefficients_inr]
  rfl

/-- The actual common root embeds in the radical factor of the full semidirect product. -/
def commonRootToPlane : commonRoot →* PlaneProduct :=
  SemidirectProduct.inl.comp (Subgroup.inclusion commonRoot_le_planeRadical)

@[simp] theorem planeLift_commonRoot (u : commonRoot) :
    planeLift (commonRootToPlane u) = u.val := by
  simp [commonRootToPlane,planeLift]

/-- Common-root restriction agrees literally with the existing actual coefficient representation. -/
theorem planeCoefficients_commonRoot (n : ℕ) (e : ℤ) :
    (planeCoefficients n e).comp commonRootToPlane = commonRepresentation n e := by
  apply MonoidHom.ext
  intro u
  change coefficientAction n e (planeLift (commonRootToPlane u)) = coefficientAction n e u.val
  rw [planeLift_commonRoot]

/-- The exact 26-covector coefficient representation restricted to the full line parabolic. -/
def lineParabolicCoefficients (n : ℕ) (e : ℤ) : Representation ℚ Q (Coefficients n) :=
  (coefficientAction n e).comp Q.subtype

/-- Pull back that actual representation along the literal semidirect multiplication map. -/
def lineCoefficients (n : ℕ) (e : ℤ) : Representation ℚ LineProduct (Coefficients n) :=
  (coefficientAction n e).comp lineLift

theorem lineCoefficients_pullback (n : ℕ) (e : ℤ) :
    lineCoefficients n e = (lineParabolicCoefficients n e).comp lineEquiv.toMonoidHom := rfl

@[simp] theorem lineCoefficients_inl (n : ℕ) (e : ℤ) (u : lineRadical) :
    lineCoefficients n e (SemidirectProduct.inl u) = coefficientAction n e u.val := by
  change coefficientAction n e (lineLift (SemidirectProduct.inl u)) = _
  simp [lineLift]

@[simp] theorem lineCoefficients_inr (n : ℕ) (e : ℤ) (q : LineLevi) :
    lineCoefficients n e (SemidirectProduct.inr q) = coefficientAction n e (lineLevi q) := by
  change coefficientAction n e (lineLift (SemidirectProduct.inr q)) = _
  simp [lineLift]

/-- Both the inverse polynomial action and the permutation of all 26 covectors are retained. -/
theorem lineCoefficients_radical_apply (n : ℕ) (e : ℤ) (u : lineRadical)
    (F : Coefficients n) (r : NonzeroCovector) :
    lineCoefficients n e (SemidirectProduct.inl u) F r =
      integralAction n e u.val (F (rowMove u.val r)) := by
  rw [lineCoefficients_inl]
  rfl

/-- The full independent-sign block matrix acts on the actual 26-covector coefficient system. -/
theorem lineCoefficients_levi_apply (n : ℕ) (e : ℤ) (q : LineLevi)
    (F : Coefficients n) (r : NonzeroCovector) :
    lineCoefficients n e (SemidirectProduct.inr q) F r =
      integralAction n e (lineElement q.1 0 q.2) (F (rowMove (lineElement q.1 0 q.2) r)) := by
  rw [lineCoefficients_inr]
  rfl

/-- The actual common root embeds in the radical factor of the full semidirect product. -/
def commonRootToLine : commonRoot →* LineProduct :=
  SemidirectProduct.inl.comp (Subgroup.inclusion commonRoot_le_lineRadical)

@[simp] theorem lineLift_commonRoot (u : commonRoot) :
    lineLift (commonRootToLine u) = u.val := by
  simp [commonRootToLine,lineLift]

/-- Common-root restriction agrees literally with the existing actual coefficient representation. -/
theorem lineCoefficients_commonRoot (n : ℕ) (e : ℤ) :
    (lineCoefficients n e).comp commonRootToLine = commonRepresentation n e := by
  apply MonoidHom.ext
  intro u
  change coefficientAction n e (lineLift (commonRootToLine u)) = coefficientAction n e u.val
  rw [lineLift_commonRoot]

/-- The actual corner inclusions into the two full parabolics. -/
def BToP : B →* P := Subgroup.inclusion inf_le_left
def BToQ : B →* Q := Subgroup.inclusion inf_le_right

def BCoefficients (n : ℕ) (e : ℤ) : Representation ℚ B (Coefficients n) :=
  (coefficientAction n e).comp B.subtype

/-- Both face restrictions are the same literal coefficient system on the actual intersection. -/
theorem planeCoefficients_restrict_B (n : ℕ) (e : ℤ) :
    (planeParabolicCoefficients n e).comp BToP = BCoefficients n e := rfl

theorem lineCoefficients_restrict_B (n : ℕ) (e : ℤ) :
    (lineParabolicCoefficients n e).comp BToQ = BCoefficients n e := rfl

def commonRootToB : commonRoot →* B := Subgroup.inclusion commonRoot_le_B

theorem BCoefficients_commonRoot (n : ℕ) (e : ℤ) :
    (BCoefficients n e).comp commonRootToB = commonRepresentation n e := rfl

end TernaryPoly.OrdinaryParabolicGroups
