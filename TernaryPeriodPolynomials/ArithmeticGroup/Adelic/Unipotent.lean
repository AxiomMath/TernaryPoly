module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Parabolic

@[expose] public section




/-! Literal two-coordinate unipotent radicals and the actual associate Weyl matrices. -/
noncomputable section
namespace GeneralEisenstein.Adelic
open Matrix
variable {R : Type*} [CommRing R]

/-- The actual plane radical in the upper (2,1) parabolic. -/
def planeUnipotent (s t : R) : GL3 R :=
  ⟨!![1,0,s;0,1,t;0,0,1], !![1,0,-s;0,1,-t;0,0,1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- The actual line radical, identical to the local standard-intertwiner coordinates. -/
abbrev lineUnipotent (s t : R) : GL3 R := upperUnipotent s t

/-- Actual lower plane-radical coordinates. -/
def lowerPlaneUnipotent (s t : R) : GL3 R :=
  ⟨!![1,0,0;0,1,0;s,t,1], !![1,0,0;0,1,0;-s,-t,1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- Actual lower line-radical coordinates. -/
def lowerLineUnipotent (s t : R) : GL3 R :=
  ⟨!![1,0,0;s,1,0;t,0,1], !![1,0,0;-s,1,0;-t,0,1], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

/-- The actual upper plane radical law is coordinate addition. -/
theorem planeUnipotent_add (s t s' t' : R) :
    planeUnipotent (s+s') (t+t') = planeUnipotent s t * planeUnipotent s' t' := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeUnipotent, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

/-- The actual upper line radical law is coordinate addition. -/
theorem lineUnipotent_add (s t s' t' : R) :
    lineUnipotent (s+s') (t+t') = lineUnipotent s t * lineUnipotent s' t' := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lineUnipotent, upperUnipotent, Matrix.mul_apply, Fin.sum_univ_three, add_comm]

/-- Genuine additive coordinate embedding into the actual plane radical. -/
def planeUnipotentHom (R : Type*) [CommRing R] : Multiplicative (R × R) →* GL3 R where
  toFun x := planeUnipotent x.toAdd.1 x.toAdd.2
  map_one' := by apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' x y := planeUnipotent_add _ _ _ _

/-- Genuine additive coordinate embedding into the actual line radical. -/
def lineUnipotentHom (R : Type*) [CommRing R] : Multiplicative (R × R) →* GL3 R where
  toFun x := lineUnipotent x.toAdd.1 x.toAdd.2
  map_one' := by apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> rfl
  map_mul' x y := lineUnipotent_add _ _ _ _

/-- The plane radical coordinate map is actually injective. -/
theorem planeUnipotentHom_injective : Function.Injective (planeUnipotentHom R) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun g : GL3 R => g.val 0 2) h
  · exact congrArg (fun g : GL3 R => g.val 1 2) h

/-- The line radical coordinate map is actually injective. -/
theorem lineUnipotentHom_injective : Function.Injective (lineUnipotentHom R) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun g : GL3 R => g.val 0 1) h
  · exact congrArg (fun g : GL3 R => g.val 0 2) h

/-- The actual plane unipotent subgroup is the image of its genuine additive coordinates. -/
def planeRadical (R : Type*) [CommRing R] : Subgroup (GL3 R) := (planeUnipotentHom R).range

/-- The actual line unipotent subgroup is the image of its genuine additive coordinates. -/
def lineRadical (R : Type*) [CommRing R] : Subgroup (GL3 R) := (lineUnipotentHom R).range

/-- Conjugating the actual line radical by the inverse associate Weyl element gives the actual
opposite plane radical, with the fixed coordinates used by the standard integral. -/
theorem weyl_inverse_lineUnipotent (s t : R) :
    weyl⁻¹ * lineUnipotent s t * weyl = lowerPlaneUnipotent s t := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, lineUnipotent, upperUnipotent, lowerPlaneUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

/-- The same genuine Weyl matrix conjugates the upper plane radical to the opposite line radical. -/
theorem weyl_planeUnipotent (s t : R) :
    weyl * planeUnipotent s t * weyl⁻¹ = lowerLineUnipotent s t := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, planeUnipotent, lowerLineUnipotent, Matrix.mul_apply, Fin.sum_univ_three]

/-- The exact associate Weyl matrix is natural under actual coefficient ring maps. -/
theorem map_weyl {S : Type*} [CommRing S] (φ : R →+* S) :
    GeneralLinearGroup.map φ (weyl : GL3 R) = (weyl : GL3 S) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weyl, GeneralLinearGroup.map_apply]

end GeneralEisenstein.Adelic

end
