module

public import TernaryPeriodPolynomials.Polynomial.IntegralTaylor.Tail
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Ring.Hom.InjSurj

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.IntegralTaylorCertificate

abbrev Poly := MvPolynomial (Fin 3) ℤ
abbrev x : Poly := X 0
abbrev y : Poly := X 1
abbrev z : Poly := X 2

/-- The literal nine-factor integer polynomial. -/
def nineFactor (r s t : Poly) : Poly :=
  (r-s)*(r+s)*(r-t)*(r+t)*(s-t)*(s+t)*(r-s-t)*(r-s+t)*(r+s-t)

/-- The three integer frames, with the differentiation coordinate supplied explicitly. -/
def frame (i : Fin 3) (t : Poly) : Fin 3 → Poly :=
  ![![z-2*y,-t,t-y], ![z-t,t-2*y,-y], ![z-2*y,y-t,t-2*y]] i

def frameA (i : Fin 3) (t : Poly) : Poly := frame i t 0+frame i t 1+frame i t 2
def frameB (i : Fin 3) (t : Poly) : Poly :=
  frame i t 0*frame i t 1+frame i t 0*frame i t 2+frame i t 1*frame i t 2
def frameC (i : Fin 3) (t : Poly) : Poly := frame i t 0*frame i t 1*frame i t 2

/-- Literal nine-factor value in the selected frame. -/
def frameF (i : Fin 3) (t : Poly) : Poly :=
  nineFactor (frame i t 0) (frame i t 1) (frame i t 2)

theorem frameF_eq_nineFactor (i : Fin 3) (t : Poly) :
    frameF i t = nineFactor (frame i t 0) (frame i t 1) (frame i t 2) := rfl

/-- The four frame groups encode `(z,[L1],y)` and `(-y,[L1,L2,L3],z)`. -/
def recordFrame : Fin 4 → Fin 3 := ![0,0,1,2]
def recordStep : Fin 4 → Poly := ![y,z,z,z]
def recordMultiplier : Fin 4 → Poly := ![z,-y,-y,-y]
def recordShift (g : Fin 4) : Fin 5 → Poly := ![0,-recordStep g,recordStep g,0,0]
def recordOrder : Fin 5 → Fin 3 := ![0,0,0,1,2]
def recordWeight (g : Fin 4) (k : Fin 5) : Poly :=
  recordMultiplier g * (![2,1,1,2*recordStep g,-2*(recordStep g)^2] k)
def recordClass : Fin 4 → Fin 5 → Fin 3 :=
  ![(fun _ => 0), ![0,2,2,0,0], (fun _ => 1), ![0,2,2,0,0]]

def recordA (g : Fin 4) (k : Fin 5) : Poly := frameA (recordFrame g) (x+recordShift g k)
def recordB (g : Fin 4) (k : Fin 5) : Poly := frameB (recordFrame g) (x+recordShift g k)
def recordC (g : Fin 4) (k : Fin 5) : Poly := frameC (recordFrame g) (x+recordShift g k)
def recordF (g : Fin 4) (k : Fin 5) : Poly := frameF (recordFrame g) (x+recordShift g k)

def referenceB : Fin 3 → Poly := ![frameB 0 x,frameB 1 x,frameB 0 (x+z)]
def referenceC : Fin 3 → Poly := ![frameC 0 x,frameC 1 x,frameC 0 (x+z)]
def deltaB (g : Fin 4) (k : Fin 5) : Poly := recordB g k-referenceB (recordClass g k)
def deltaC (g : Fin 4) (k : Fin 5) : Poly := recordC g k-referenceC (recordClass g k)

def halfB : Fin 4 → Fin 5 → Poly :=
  ![![0,
    x*y + (-1)*y^2,
    (-1)*x*y,
    0,
    0],
    ![0,
    2*x*z + (-1)*y*z,
    0,
    0,
    0],
    ![0,
    x*z + (-1)*y*z + (-1)*z^2,
    (-1)*x*z + y*z,
    0,
    0],
    ![x*y + (-1)*y^2,
    x*y + 2*x*z + (-1)*y^2 + (-2)*y*z,
    x*y + (-1)*y^2 + y*z,
    x*y + (-1)*y^2,
    x*y + (-1)*y^2]]
def halfC : Fin 4 → Fin 5 → Poly :=
  ![![0,
    (-2)*x*y^2 + x*y*z + 2*y^3 + (-1)*y^2*z,
    2*x*y^2 + (-1)*x*y*z,
    0,
    0],
    ![0,
    (-4)*x*y*z + 2*x*z^2 + 2*y^2*z + (-1)*y*z^2,
    0,
    0,
    0],
    ![0,
    (-1)*x*y*z + y^2*z + y*z^2,
    x*y*z + (-1)*y^2*z,
    0,
    0],
    ![(-2)*x*y^2 + x*y*z + 2*y^3 + (-1)*y^2*z,
    (-2)*x*y^2 + (-3)*x*y*z + 2*x*z^2 + 2*y^3 + 3*y^2*z + (-2)*y*z^2,
    (-2)*x*y^2 + x*y*z + 2*y^3 + (-3)*y^2*z + y*z^2,
    (-2)*x*y^2 + x*y*z + 2*y^3 + (-1)*y^2*z,
    (-2)*x*y^2 + x*y*z + 2*y^3 + (-1)*y^2*z]]

/-- Every record has the same first elementary coordinate, independent of x. -/
theorem recordA_eq (g : Fin 4) (k : Fin 5) : recordA g k = z-3*y := by
  fin_cases g <;> fin_cases k <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, recordA,recordFrame,recordShift,recordStep,frameA,frame] <;> ring

/-- The record's second coordinate agrees modulo two with its assigned reference. -/
theorem deltaB_eq_two_mul (g : Fin 4) (k : Fin 5) : deltaB g k = 2*halfB g k := by
  fin_cases g <;> fin_cases k <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, deltaB,recordB,referenceB,recordClass,recordFrame,recordShift,recordStep,frameB,frame,halfB] <;> ring

/-- The record's third coordinate agrees modulo two with its assigned reference. -/
theorem deltaC_eq_two_mul (g : Fin 4) (k : Fin 5) : deltaC g k = 2*halfC g k := by
  fin_cases g <;> fin_cases k <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, deltaC,recordC,referenceC,recordClass,recordFrame,recordShift,recordStep,frameC,frame,halfC] <;> ring

theorem record_differences_even (g : Fin 4) (k : Fin 5) :
    (2 : Poly) ∣ deltaB g k ∧ (2 : Poly) ∣ deltaC g k :=
  ⟨⟨halfB g k,deltaB_eq_two_mul g k⟩,⟨halfC g k,deltaC_eq_two_mul g k⟩⟩

/-- The chain formula differentiates the actual frame, holding the reference pair fixed. -/
def recordTaylorValue (g : Fin 4) (k : Fin 5) (i j : ℕ) : Poly :=
  let F := recordF g k
  let P := IntegralTaylorTail.powerTerm (deltaB g k) (deltaC g k) i j
  let D := IntegralTaylorTail.firstTerm (deltaB g k) (deltaC g k)
    (pderiv 0 (recordB g k)) (pderiv 0 (recordC g k)) i j
  let DD := IntegralTaylorTail.secondTerm (deltaB g k) (deltaC g k)
    (pderiv 0 (recordB g k)) (pderiv 0 (recordC g k))
    (pderiv 0 (pderiv 0 (recordB g k))) (pderiv 0 (pderiv 0 (recordC g k))) i j
  ![F*P, pderiv 0 F*P+F*D,
    pderiv 0 (pderiv 0 F)*P+2*pderiv 0 F*D+F*DD] (recordOrder k)

/-- Sum of the twenty literal records restricted to one residue class. -/
def localCoeff (point : Fin 3) (i j : ℕ) : Poly :=
  ∑ g : Fin 4, ∑ k : Fin 5, if recordClass g k = point then
    recordWeight g k*recordTaylorValue g k i j else 0

def jetI : Fin 6 → ℕ := ![0,1,0,2,1,0]
def jetJ : Fin 6 → ℕ := ![0,0,1,0,1,2]

def alpha : Poly := y+z
def U : Poly := y*alpha^2*(x+z)*(x+y+z)
def V : Poly := z*alpha*(x+y)*(x+y+z)
def W : Poly := x*y^2*(x+y)*alpha
def expectedBase : Fin 3 → Poly := ![(x+y)*y*U^2,(x+y)*y*z*alpha*V^2,(x+y)*alpha*W^2]
def expected (point : Fin 3) : Fin 6 → Poly :=
  ![0,expectedBase point, (![z,y,z] point)*expectedBase point,0,0,0]


end TernaryPoly.IntegralTaylorCertificate
