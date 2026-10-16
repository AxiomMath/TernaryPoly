module

public import TernaryPeriodPolynomials.Polynomial.BivariateTaylorTruncation
public import TernaryPeriodPolynomials.Building.Integer.ToddNumerator
public import TernaryPeriodPolynomials.Polynomial.IntegralTaylor.CertificateProofs
public import TernaryPeriodPolynomials.AlternatingSolution.OddDegree.Integral
public import TernaryPeriodPolynomials.ArithmeticGroup.ElementaryCoordinates
public import TernaryPeriodPolynomials.Polynomial.CharTwo.ToddSymbol

@[expose] public section

open MvPolynomial
open scoped BigOperators
noncomputable section
namespace TernaryPoly.IntegralToddSymbol
open IntegralTaylorCertificate
open BivariateTaylorTruncation

/-- Introduce a separate differentiation variable; the target coordinates stay in coefficients. -/
def liftX : Poly →+* Polynomial Poly :=
  eval₂Hom (Polynomial.C.comp MvPolynomial.C) ![Polynomial.X,Polynomial.C y,Polynomial.C z]

/-- Substitute only the first ordinary coordinate. -/
def atX (t : Poly) : Poly →ₐ[ℤ] Poly := bind₁ ![t,y,z]

@[simp] theorem liftX_C (n : ℤ) : liftX (MvPolynomial.C n) = Polynomial.C (MvPolynomial.C n) := by
  simp [liftX]
@[simp] theorem liftX_x : liftX x = Polynomial.X := by simp [liftX,x]
@[simp] theorem liftX_y : liftX y = Polynomial.C y := by simp [liftX,y]
@[simp] theorem liftX_z : liftX z = Polynomial.C z := by simp [liftX,z]

theorem eval_liftX (p t : Poly) : Polynomial.eval t (liftX p) = atX t p := by
  induction p using MvPolynomial.induction_on with
  | C n => simp [atX]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,Polynomial.eval_mul,hp]
    congr 1
    fin_cases i <;> simp [atX,y,z,liftX]

theorem atX_x (p : Poly) : atX x p = p := by
  have he : ![x,y,z] = (X : Fin 3 → Poly) := by
    funext i
    fin_cases i <;> rfl
  simp [atX,he]

theorem derivative_liftX (p : Poly) : Polynomial.derivative (liftX p) = liftX (pderiv 0 p) := by
  induction p using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,pderiv_mul,Polynomial.derivative_mul,map_add,hp]
    fin_cases i <;> simp [liftX,y,z,mul_comm]

theorem pderiv_atX (p u : Poly) (hu : pderiv 0 u = 0) :
    pderiv 0 (atX (x+u) p) = atX (x+u) (pderiv 0 p) := by
  induction p using MvPolynomial.induction_on with
  | C n => simp [atX]
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,pderiv_mul,map_add,hp]
    fin_cases i <;> simp [atX,x,y,z,hu]

theorem atX_frame (i : Fin 3) (t : Poly) (j : Fin 3) :
    atX t (frame i x j) = frame i t j := by
  fin_cases i <;> fin_cases j <;> simp [frame,atX,x,y,z,map_ofNat]

theorem atX_frameB (i : Fin 3) (t : Poly) : atX t (frameB i x) = frameB i t := by
  simp only [frameB,map_add,map_mul,atX_frame]
theorem atX_frameC (i : Fin 3) (t : Poly) : atX t (frameC i x) = frameC i t := by
  simp only [frameC,map_mul,atX_frame]
theorem atX_frameF (i : Fin 3) (t : Poly) : atX t (frameF i x) = frameF i t := by
  simp only [frameF_eq_nineFactor,nineFactor,map_mul,map_add,map_sub,atX_frame]

theorem frameA_eq (i : Fin 3) (t : Poly) : frameA i t = z-3*y := by
  fin_cases i <;> simp [frameA,frame] <;> ring

/-- Freeze the first elementary coordinate before expanding in the other two. -/
def freezeA (P : Poly) : MvPolynomial (Fin 2) Poly :=
  eval₂ (MvPolynomial.C.comp MvPolynomial.C) ![MvPolynomial.C (z-3*y),X 0,X 1] P

theorem eval_freezeA (P : Poly) (b c : Poly) :
    eval ![b,c] (freezeA P) = bind₁ ![z-3*y,b,c] P := by
  induction P using MvPolynomial.induction_on with
  | C n => simp only [freezeA,eval₂_C,RingHom.comp_apply,eval_C,bind₁_C_right]
  | add p q hp hq => simp_all [freezeA,eval₂_add]
  | mul_X p i hp => fin_cases i <;> simp_all [freezeA,eval₂_mul]

theorem pderiv_freezeA (P : Poly) (i : Fin 2) :
    pderiv i (freezeA P) = freezeA (pderiv i.succ P) := by
  induction P using MvPolynomial.induction_on with
  | C n => simp only [freezeA,eval₂_C,RingHom.comp_apply,pderiv_C,eval₂_zero]
  | add p q hp hq => simp_all [freezeA,eval₂_add]
  | mul_X p j hp =>
    fin_cases i <;> fin_cases j <;> simp_all [freezeA,eval₂_mul]

/-- Formal source evaluation at the exact integer reference triple. -/
def referenceEval (point : Fin 3) : Poly →ₐ[ℤ] Poly :=
  bind₁ ![z-3*y,referenceB point,referenceC point]

def taylorCoefficient (P : Poly) (point : Fin 3) (jet : Fin 6) : Poly :=
  (shiftedTaylor (freezeA P) (referenceB point) (referenceC point)).coeff (lowExponent jet)

theorem taylorCoefficient_zero (P : Poly) (point : Fin 3) :
    taylorCoefficient P point 0 = referenceEval point P := by
  simpa [taylorCoefficient,lowExponent,binaryExponent,referenceEval] using
    (shiftedTaylor_coeff_zero (freezeA P) (referenceB point) (referenceC point)).trans
      (eval_freezeA P _ _)

theorem taylorCoefficient_one (P : Poly) (point : Fin 3) :
    taylorCoefficient P point 1 = referenceEval point (pderiv 1 P) := by
  simpa [taylorCoefficient,lowExponent,binaryExponent,referenceEval,pderiv_freezeA] using
    (shiftedTaylor_coeff_single (freezeA P) (referenceB point) (referenceC point) 0).trans
      (by rw [pderiv_freezeA]; exact eval_freezeA _ _ _)

theorem taylorCoefficient_two (P : Poly) (point : Fin 3) :
    taylorCoefficient P point 2 = referenceEval point (pderiv 2 P) := by
  simpa [taylorCoefficient,lowExponent,binaryExponent,referenceEval,pderiv_freezeA] using
    (shiftedTaylor_coeff_single (freezeA P) (referenceB point) (referenceC point) 1).trans
      (by rw [pderiv_freezeA]; exact eval_freezeA _ _ _)

/-- The ordinary frame applied to an arbitrary integer polynomial. -/
def ordinaryFrame (i : Fin 3) (P : Poly) : Poly := bind₁ (frame i x) P

theorem ordinaryFrame_factor (i : Fin 3) (P : Poly) :
    ordinaryFrame i (integerNineFactor*ternaryElementaryEval P) =
      frameF i x * bind₁ ![z-3*y,frameB i x,frameC i x] P := by
  have he : ordinaryFrame i (ternaryElementaryEval P) =
      bind₁ ![frameA i x,frameB i x,frameC i x] P := by
    induction P using MvPolynomial.induction_on with
    | C n => simp [ordinaryFrame,ternaryElementaryEval]
    | add p q hp hq => simp_all [ordinaryFrame,ternaryElementaryEval]
    | mul_X p j hp =>
      fin_cases j <;> simp_all [ordinaryFrame,ternaryElementaryEval,frameA,frameB,frameC]
  rw [frameA_eq] at he
  change bind₁ (frame i x) (_*_) = _
  rw [map_mul,show bind₁ (frame i x) (ternaryElementaryEval P) = _ from he]
  congr 1
  simp only [integerNineFactor,map_mul,map_add,map_sub,bind₁_X_right]
  exact (frameF_eq_nineFactor i x).symm

theorem liftX_freezeA_eval (P b c : Poly) :
    liftX (bind₁ ![z-3*y,b,c] P) =
      eval₂ Polynomial.C ![liftX b,liftX c] (freezeA P) := by
  induction P using MvPolynomial.induction_on with
  | C n => simp only [freezeA,eval₂_C,RingHom.comp_apply,bind₁_C_right,liftX_C]
  | add p q hp hq => simp_all [freezeA,eval₂_add]
  | mul_X p i hp => fin_cases i <;> simp_all [freezeA,eval₂_mul,liftX,map_ofNat]

theorem liftX_ordinaryFrame (i : Fin 3) (P : Poly) :
    liftX (ordinaryFrame i (integerNineFactor*ternaryElementaryEval P)) =
      liftX (frameF i x) * eval₂ Polynomial.C ![liftX (frameB i x),liftX (frameC i x)] (freezeA P) := by
  rw [ordinaryFrame_factor,map_mul,liftX_freezeA_eval]

private theorem map_b4Operator {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (u : R) (p : Polynomial R) :
    Polynomial.map φ (ToddIntegralCongruences.b4Operator u p) =
      ToddIntegralCongruences.b4Operator (φ u) (Polynomial.map φ p) := by
  simp only [ToddIntegralCongruences.b4Operator,Polynomial.map_sub,Polynomial.map_add,
    Polynomial.map_smul,Polynomial.map_taylor,← Polynomial.derivative_map,map_mul,map_pow,
    map_neg,map_ofNat]

private theorem b4Operator_add {R : Type*} [CommRing R]
    (u : R) (p q : Polynomial R) :
    ToddIntegralCongruences.b4Operator u (p+q) =
      ToddIntegralCongruences.b4Operator u p+ToddIntegralCongruences.b4Operator u q := by
  simp only [ToddIntegralCongruences.b4Operator,map_add,smul_add]
  abel

private def parameterLift : MvPolynomial (Fin 2) ℤ →+* Poly := (rename Fin.succ).toRingHom

private theorem liftX_finSucc (P : Poly) :
    liftX P = Polynomial.map parameterLift (finSuccEquiv ℤ 2 P) := by
  have h1 : finSuccEquiv ℤ 2 (X (1 : Fin 3)) = Polynomial.C (X (0 : Fin 2)) :=
    finSuccEquiv_X_succ (j := 0)
  have h2 : finSuccEquiv ℤ 2 (X (2 : Fin 3)) = Polynomial.C (X (1 : Fin 2)) :=
    finSuccEquiv_X_succ (j := 1)
  induction P using MvPolynomial.induction_on with
  | C n => simp [parameterLift]
  | add p q hp hq => simp only [map_add,Polynomial.map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,Polynomial.map_mul,hp]
    congr 1
    fin_cases i <;> simp [h1,h2,finSuccEquiv_X_zero,parameterLift,liftX,y,z]

/-- The transported B₄ numerator is exactly the four groups of frame operators. -/
theorem integerN4_frame_sum (P : Poly) :
    IntegerToddNumerator.integerN4 P =
      ∑ g : Fin 4, recordMultiplier g * Polynomial.eval x
        (ToddIntegralCongruences.b4Operator (recordStep g) (liftX (ordinaryFrame (recordFrame g) P))) := by
  have he : IntegerToddNumerator.integerN4 P = Polynomial.eval x
      (liftX (IntegerToddNumerator.integerN4 P)) := by rw [eval_liftX,atX_x]
  rw [he,liftX_finSucc,IntegerToddNumerator.integerN4,AlgEquiv.apply_symm_apply]
  simp only [Polynomial.map_sub,Polynomial.map_smul,map_b4Operator]
  rw [← liftX_finSucc,← liftX_finSucc]
  simp only [Polynomial.eval_sub,Polynomial.eval_smul,smul_eq_mul]
  simp [Fin.sum_univ_succ,recordMultiplier,recordStep,recordFrame,
    IntegerToddNumerator.integerFrame1,IntegerToddNumerator.integerFrame2,ordinaryFrame,frame,
    map_add,b4Operator_add,parameterLift,x,y,z]
  ring

/-- Remove exactly the factor two already included in each differentiated record. -/
def normalizedWeight (g : Fin 4) (k : Fin 5) : Poly :=
  recordMultiplier g * (![2,1,1,recordStep g,-(recordStep g)^2] k)

def fullRecord (P : Poly) (g : Fin 4) (k : Fin 5) : Poly :=
  normalizedWeight g k * record (liftX (frameF (recordFrame g) x)) (x+recordShift g k)
    (recordOrder k)
    (eval₂ Polynomial.C ![liftX (frameB (recordFrame g) x),liftX (frameC (recordFrame g) x)] (freezeA P))

/-- Expanding the five terms of B₄ gives the twenty actual derivative records. -/
theorem integerN4_record_sum (P : Poly) :
    IntegerToddNumerator.integerN4 (integerNineFactor*ternaryElementaryEval P) =
      ∑ g : Fin 4, ∑ k : Fin 5, fullRecord P g k := by
  rw [integerN4_frame_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [liftX_ordinaryFrame]
  simp [fullRecord,normalizedWeight,record,recordShift,recordOrder,
    Fin.sum_univ_succ,ToddIntegralCongruences.b4Operator,Polynomial.taylor_eval]
  ring

private theorem record_chain_formula {R : Type*} [CommRing R]
    (F B D : Polynomial R) (t : R) (i j : ℕ) (k : Fin 3) :
    record F t k (IntegralTaylorTail.powerTerm B D i j) =
      ![Polynomial.eval t F * IntegralTaylorTail.powerTerm (Polynomial.eval t B) (Polynomial.eval t D) i j,
        2*(Polynomial.eval t F.derivative * IntegralTaylorTail.powerTerm (Polynomial.eval t B) (Polynomial.eval t D) i j +
          Polynomial.eval t F * IntegralTaylorTail.firstTerm (Polynomial.eval t B) (Polynomial.eval t D)
            (Polynomial.eval t B.derivative) (Polynomial.eval t D.derivative) i j),
        2*(Polynomial.eval t F.derivative.derivative * IntegralTaylorTail.powerTerm (Polynomial.eval t B) (Polynomial.eval t D) i j +
          2*Polynomial.eval t F.derivative * IntegralTaylorTail.firstTerm (Polynomial.eval t B) (Polynomial.eval t D)
            (Polynomial.eval t B.derivative) (Polynomial.eval t D.derivative) i j +
          Polynomial.eval t F * IntegralTaylorTail.secondTerm (Polynomial.eval t B) (Polynomial.eval t D)
            (Polynomial.eval t B.derivative) (Polynomial.eval t D.derivative)
            (Polynomial.eval t B.derivative.derivative) (Polynomial.eval t D.derivative.derivative) i j)] k := by
  fin_cases k
  · simp [record,IntegralTaylorTail.powerTerm]
  · change 2*Polynomial.eval t (Polynomial.derivative (F*IntegralTaylorTail.powerTerm B D i j)) = _
    rw [IntegralTaylorTail.derivative_mul_powerTerm]
    simp [IntegralTaylorTail.powerTerm,IntegralTaylorTail.firstTerm]
  · change 2*Polynomial.eval t (Polynomial.derivative (Polynomial.derivative
      (F*IntegralTaylorTail.powerTerm B D i j))) = _
    rw [IntegralTaylorTail.derivative_twice_mul_powerTerm]
    simp [IntegralTaylorTail.powerTerm,IntegralTaylorTail.firstTerm,IntegralTaylorTail.secondTerm]

theorem recordShift_pderiv (g : Fin 4) (k : Fin 5) : pderiv 0 (recordShift g k) = 0 := by
  fin_cases g <;> fin_cases k <;> simp [recordShift,recordStep,y,z]

private theorem eval_derivative_liftX (p u : Poly) (hu : pderiv 0 u = 0) :
    Polynomial.eval (x+u) (Polynomial.derivative (liftX p)) = pderiv 0 (atX (x+u) p) := by
  rw [derivative_liftX,eval_liftX,pderiv_atX p u hu]

private theorem eval_derivative_twice_liftX (p u : Poly) (hu : pderiv 0 u = 0) :
    Polynomial.eval (x+u) (Polynomial.derivative (Polynomial.derivative (liftX p))) =
      pderiv 0 (pderiv 0 (atX (x+u) p)) := by
  rw [derivative_liftX,eval_derivative_liftX _ u hu,pderiv_atX p u hu]

/-- The normalized univariate Taylor record is exactly the finite table's fixed-reference chain record. -/
theorem weighted_record_powerTerm (g : Fin 4) (k : Fin 5) (i j : ℕ) :
    normalizedWeight g k * record (liftX (frameF (recordFrame g) x)) (x+recordShift g k)
      (recordOrder k) (IntegralTaylorTail.powerTerm
        (liftX (frameB (recordFrame g) x)-Polynomial.C (referenceB (recordClass g k)))
        (liftX (frameC (recordFrame g) x)-Polynomial.C (referenceC (recordClass g k))) i j) =
      recordWeight g k*recordTaylorValue g k i j := by
  rw [record_chain_formula]
  have hu := recordShift_pderiv g k
  simp only [Polynomial.derivative_sub,Polynomial.derivative_C,sub_zero,
    eval_derivative_twice_liftX _ _ hu,eval_derivative_liftX _ _ hu,
    Polynomial.eval_sub,Polynomial.eval_C,eval_liftX,atX_frameF,atX_frameB,atX_frameC]
  change normalizedWeight g k *
    ![recordF g k*IntegralTaylorTail.powerTerm (deltaB g k) (deltaC g k) i j,
      2*(pderiv 0 (recordF g k)*IntegralTaylorTail.powerTerm (deltaB g k) (deltaC g k) i j +
        recordF g k*IntegralTaylorTail.firstTerm (deltaB g k) (deltaC g k)
          (pderiv 0 (recordB g k)) (pderiv 0 (recordC g k)) i j),
      2*(pderiv 0 (pderiv 0 (recordF g k))*IntegralTaylorTail.powerTerm (deltaB g k) (deltaC g k) i j +
        2*pderiv 0 (recordF g k)*IntegralTaylorTail.firstTerm (deltaB g k) (deltaC g k)
          (pderiv 0 (recordB g k)) (pderiv 0 (recordC g k)) i j +
        recordF g k*IntegralTaylorTail.secondTerm (deltaB g k) (deltaC g k)
          (pderiv 0 (recordB g k)) (pderiv 0 (recordC g k))
          (pderiv 0 (pderiv 0 (recordB g k))) (pderiv 0 (pderiv 0 (recordC g k))) i j)] (recordOrder k) = _
  fin_cases k <;> simp [normalizedWeight,recordWeight,recordTaylorValue,recordOrder] <;> ring

private theorem lowExponent_jetI (k : Fin 6) : (lowExponent k) 0 = jetI k := by
  fin_cases k <;> simp [lowExponent,jetI]
private theorem lowExponent_jetJ (k : Fin 6) : (lowExponent k) 1 = jetJ k := by
  fin_cases k <;> simp [lowExponent,jetJ]

/-- Apply the universal high-tail theorem to one actual integer B₄ record. -/
theorem fullRecord_truncation (P : Poly) (g : Fin 4) (k : Fin 5) :
    (8 : Poly) ∣ fullRecord P g k - ∑ jet : Fin 6,
      taylorCoefficient P (recordClass g k) jet *
        (recordWeight g k*recordTaylorValue g k (jetI jet) (jetJ jet)) := by
  have h := record_taylor_truncation (freezeA P) (referenceB (recordClass g k))
    (referenceC (recordClass g k)) (liftX (frameF (recordFrame g) x))
    (liftX (frameB (recordFrame g) x)) (liftX (frameC (recordFrame g) x)) (x+recordShift g k)
    (by simpa only [eval_liftX,atX_frameB,recordB,deltaB] using (record_differences_even g k).1)
    (by simpa only [eval_liftX,atX_frameC,recordC,deltaC] using (record_differences_even g k).2)
    (recordOrder k)
  have hw := dvd_mul_of_dvd_right h (normalizedWeight g k)
  rw [mul_sub,Finset.mul_sum] at hw
  have he : (∑ jet : Fin 6, normalizedWeight g k *
      (taylorCoefficient P (recordClass g k) jet * record (liftX (frameF (recordFrame g) x))
        (x+recordShift g k) (recordOrder k) (IntegralTaylorTail.powerTerm
          (liftX (frameB (recordFrame g) x)-Polynomial.C (referenceB (recordClass g k)))
          (liftX (frameC (recordFrame g) x)-Polynomial.C (referenceC (recordClass g k)))
          ((lowExponent jet) 0) ((lowExponent jet) 1)))) =
      ∑ jet : Fin 6, taylorCoefficient P (recordClass g k) jet *
        (recordWeight g k*recordTaylorValue g k (jetI jet) (jetJ jet)) := by
    apply Finset.sum_congr rfl
    intro jet hj
    rw [mul_left_comm,weighted_record_powerTerm,lowExponent_jetI,lowExponent_jetJ]
  change (8 : Poly) ∣ fullRecord P g k - _ at hw
  dsimp only [taylorCoefficient] at he
  rw [he] at hw
  exact hw

/-- Reassemble all twenty records and all degrees into the finite eighteen-entry coefficient table. -/
theorem integerN4_taylor_table (P : Poly) :
    (8 : Poly) ∣ IntegerToddNumerator.integerN4 (integerNineFactor*ternaryElementaryEval P) -
      ∑ point : Fin 3, ∑ jet : Fin 6, taylorCoefficient P point jet * localCoeff point (jetI jet) (jetJ jet) := by
  have h := Finset.dvd_sum (s := Finset.univ) (fun g _ =>
    Finset.dvd_sum (s := Finset.univ) (fun k _ => fullRecord_truncation P g k))
  simp only [Finset.sum_sub_distrib] at h
  rw [← integerN4_record_sum] at h
  have he : (∑ g : Fin 4, ∑ k : Fin 5, ∑ jet : Fin 6,
      taylorCoefficient P (recordClass g k) jet *
        (recordWeight g k*recordTaylorValue g k (jetI jet) (jetJ jet))) =
      ∑ point : Fin 3, ∑ jet : Fin 6, taylorCoefficient P point jet * localCoeff point (jetI jet) (jetJ jet) := by
    simp only [localCoeff,Finset.mul_sum,mul_ite,mul_zero]
    trans ∑ jet : Fin 6, ∑ g : Fin 4, ∑ k : Fin 5,
      taylorCoefficient P (recordClass g k) jet *
        (recordWeight g k*recordTaylorValue g k (jetI jet) (jetJ jet))
    · symm
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g hg
      rw [Finset.sum_comm]
    · conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro jet hj
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g hg
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      simp
  rwa [he] at h

/-- The integer lift read from the six surviving entries of the finite coefficient table. -/
def symbolLift (P : Poly) : Poly :=
  ∑ point : Fin 3, expectedBase point *
    (referenceEval point (pderiv 1 P) + (![z,y,z] point)*referenceEval point (pderiv 2 P))

theorem taylor_expected_sum (P : Poly) :
    (∑ point : Fin 3, ∑ jet : Fin 6, taylorCoefficient P point jet * expected point jet) =
      symbolLift P := by
  apply Finset.sum_congr rfl
  intro point hp
  simp [Fin.sum_univ_succ,expected,taylorCoefficient_one,taylorCoefficient_two]
  ring

/-- Reduction of integer source and target coefficients modulo two. -/
abbrev mapTwo : Poly →+* CharTwoToddSymbol.Poly := MvPolynomial.map (Int.castRingHom (ZMod 2))

def reducedReference (point : Fin 3) : Fin 3 → CharTwoToddSymbol.Poly :=
  let x := CharTwoToddSymbol.x
  let y := CharTwoToddSymbol.y
  let z := CharTwoToddSymbol.z
  let a := CharTwoToddSymbol.alpha
  ![![a,x^2+x*y+y*z,z*x*(x+y)], ![a,x^2+x*z+y*z,x*y*(x+z)],
    ![a,x^2+x*y+z^2,z*(x+z)*(x+y+z)]] point

theorem mapTwo_reference_coordinates (point : Fin 3) (i : Fin 3) :
    mapTwo (![z-3*y,referenceB point,referenceC point] i) = reducedReference point i := by
  fin_cases point <;> fin_cases i <;>
    simp [mapTwo,reducedReference,referenceB,referenceC,frameB,frameC,frame,
      x,y,z,CharTwoToddSymbol.x,CharTwoToddSymbol.y,CharTwoToddSymbol.z,CharTwoToddSymbol.alpha,
      CharTwo.sub_eq_add] <;> ring_nf <;> simp only [CharTwo.ofNat_eq_mod] <;>
      norm_num <;> simp only [CharTwo.neg_eq,CharTwo.sub_eq_add]

theorem mapTwo_referenceEval (P : Poly) (point : Fin 3) :
    mapTwo (referenceEval point P) = bind₁ (reducedReference point) (mapTwo P) := by
  rw [referenceEval,mapTwo,map_bind₁]
  congr 2
  funext i
  exact mapTwo_reference_coordinates point i

/-- The lift has precisely the characteristic-two symbol required by the odd branch. -/
theorem mapTwo_symbolLift (P : Poly) :
    mapTwo (symbolLift P) = CharTwoToddSymbol.jSymbol (mapTwo P) := by
  simp only [symbolLift,map_sum,map_mul,map_add,mapTwo_referenceEval,← pderiv_map]
  simp [Fin.sum_univ_three,expectedBase,U,V,W,alpha,x,y,z,mapTwo,reducedReference,
    CharTwoToddSymbol.jSymbol,CharTwoToddSymbol.reducedSymbol,CharTwoToddSymbol.evalU,
    CharTwoToddSymbol.evalV,CharTwoToddSymbol.evalW,CharTwoToddSymbol.U,
    CharTwoToddSymbol.V,CharTwoToddSymbol.W,CharTwoToddSymbol.alpha,
    CharTwoToddSymbol.x,CharTwoToddSymbol.y,CharTwoToddSymbol.z]
  ring

/-- Cancel four over the integer polynomial ring before reducing modulo two. -/
theorem mapTwo_zero_of_eight_dvd_four (P : Poly) (h : (8 : Poly) ∣ 4*P) : mapTwo P = 0 := by
  obtain ⟨Q,hQ⟩ := h
  have he : P = 2*Q := by
    apply mul_left_cancel₀ (show (4 : Poly) ≠ 0 by norm_num)
    calc 4*P = 8*Q := hQ
         _ = 4*(2*Q) := by ring
  simp [he,mapTwo,CharTwo.two_eq_zero]

/-- The universal reduction consumes exactly the finite eighteen-entry congruence. -/
theorem integerN4_symbol_congruence_of_table (P : Poly)
    (hcert : ∀ point : Fin 3, ∀ jet : Fin 6,
      (8 : Poly) ∣ localCoeff point (jetI jet) (jetJ jet)-4*expected point jet) :
    (8 : Poly) ∣ IntegerToddNumerator.integerN4
      (integerNineFactor*ternaryElementaryEval P)-4*symbolLift P := by
  have h := Finset.dvd_sum (s := Finset.univ) (fun point _ =>
    Finset.dvd_sum (s := Finset.univ) (fun jet _ =>
      dvd_mul_of_dvd_right (hcert point jet) (taylorCoefficient P point jet)))
  simp only [mul_sub,Finset.sum_sub_distrib] at h
  have he : (∑ point : Fin 3, ∑ jet : Fin 6,
      taylorCoefficient P point jet*(4*expected point jet)) = 4*symbolLift P := by
    rw [← taylor_expected_sum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro point hp
    apply Finset.sum_congr rfl
    intro jet hj
    ring
  rw [he] at h
  convert dvd_add (integerN4_taylor_table P) h using 1
  ring

/-- Once the exact numerator congruence is established, whole Todd vanishing kills the full symbol. -/
theorem jSymbol_zero_of_numerator_congruence (P : Poly)
    (hcong : (8 : Poly) ∣ IntegerToddNumerator.integerN4
      (integerNineFactor*ternaryElementaryEval P) - 4*symbolLift P)
    (hzero : alternatingTodd (ToddIntegralCongruences.integerCoefficientMap
      (integerNineFactor*ternaryElementaryEval P)) = 0) :
    CharTwoToddSymbol.jSymbol (mapTwo P) = 0 := by
  have hnum := IntegerToddNumerator.integerN4_dvd_eight _ hzero
  have h : (8 : Poly) ∣ 4*symbolLift P := by
    convert dvd_sub hnum hcong using 1
    ring
  rw [← mapTwo_symbolLift]
  exact mapTwo_zero_of_eight_dvd_four _ h

/-- The entire integer numerator has the predicted first-order residue in every degree. -/
theorem integerN4_symbol_congruence (P : Poly) :
    (8 : Poly) ∣ IntegerToddNumerator.integerN4
      (integerNineFactor*ternaryElementaryEval P)-4*symbolLift P := by
  apply integerN4_symbol_congruence_of_table P
  intro point jet
  refine ⟨certificateQuotient point jet, ?_⟩
  rw [coefficient_certificate]
  ring

/-- Whole rational Todd vanishing forces the full characteristic-two first-order symbol to vanish. -/
theorem jSymbol_zero_of_alternatingTodd (P : Poly)
    (hzero : alternatingTodd (ToddIntegralCongruences.integerCoefficientMap
      (integerNineFactor*ternaryElementaryEval P)) = 0) :
    CharTwoToddSymbol.jSymbol (mapTwo P) = 0 :=
  jSymbol_zero_of_numerator_congruence P (integerN4_symbol_congruence P) hzero

end TernaryPoly.IntegralToddSymbol
