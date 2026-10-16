module

public import TernaryPeriodPolynomials.SymmetricSolution.Odd.Seed
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Tactic.FieldSimp

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricOddRationalSeed

abbrev TP := TernaryPolynomial
abbrev BP := MvPolynomial (Fin 2) ℚ
abbrev Frac := FractionRing TP
abbrev embed : TP →+* Frac := algebraMap TP Frac

/-- The actual single-pole first seed of the lowest odd layer. -/
def P (q : BP) (a b c : TP) : Frac := embed (binaryLiftEval q b c) / embed a

/-- The already cancelled polynomial second seed, evaluated in literal coordinates. -/
def Q (q : BP) (hq : SymmetricBinaryPeriodRelations q) (a b c : TP) : TP :=
  substitute3 (symmetricOddSeedQ q hq) a b c

theorem Q_mul (q : BP) (hq : SymmetricBinaryPeriodRelations q) (a b c : TP) :
    (a+b)*Q q hq a b c=binaryLiftEval q a c+binaryLiftEval q b c := by
  have h := congrArg (fun p => substitute3 p a b c) (symmetricOddSeedQ_mul q hq)
  rw [symmetricPeriodSeedQ_substitute] at h
  simpa only [Q,substitute3,map_mul,map_add,bind₁_X_right,
    Matrix.cons_val_zero,Matrix.cons_val_one,pow_zero,one_mul] using h

theorem P_swap (q : BP) (hq : SymmetricBinaryPeriodRelations q) (a b c : TP) :
    P q a c b = P q a b c := by
  simp only [P,symmetricBinaryEval_swap hq b c]

theorem P_odd_second (q : BP) (hq : SymmetricBinaryPeriodRelations q) (a b c : TP) :
    P q a (-b) c = -P q a b c := by
  simp only [P,symmetricBinaryEval_neg_first hq,map_neg,neg_div]

theorem P_odd_third (q : BP) (hq : SymmetricBinaryPeriodRelations q) (a b c : TP) :
    P q a b (-c) = -P q a b c := by
  simp only [P,symmetricBinaryEval_neg_second hq,map_neg,neg_div]

theorem P_odd_first (q : BP) (a b c : TP) : P q (-a) b c = -P q a b c := by
  simp only [P,map_neg,div_neg]

/-- The literal last-two-variable norm vanishes even before any pole cancellation. -/
theorem P_norm (q : BP) (hq : SymmetricBinaryPeriodRelations q) (a b c : TP) :
    P q a b c+P q a (-c) (b-c)+P q a (c-b) (-b)=0 := by
  have h := symmetricPeriodSeedP_norm 0 hq a b c
  simp only [symmetricPeriodSeedP_substitute,pow_zero,one_mul] at h
  unfold P
  rw [←add_div,←add_div,←map_add,←map_add,h,map_zero,zero_div]

/-- The rational first seed and polynomial second seed satisfy the exact second mixed equation. -/
theorem P_mixed (q : BP) (hq : SymmetricBinaryPeriodRelations q) (a b c : TP)
    (ha : a ≠ 0) : P q a (c+a) b-P q a c b=embed (Q q hq (-c) (a+c) b) := by
  have h := Q_mul q hq (-c) (a+c) b
  rw [show -c+(a+c)=a by ring,symmetricBinaryEval_neg_first hq] at h
  have ha' : embed a≠0 := by simpa only [map_zero] using (IsFractionRing.injective TP Frac).ne ha
  unfold P
  rw [show c+a=a+c by ring,←sub_div,←map_sub,div_eq_iff ha']
  rw [←map_mul]
  apply congrArg embed
  linear_combination -h

/-- Being polynomial is exactly divisibility of the numerator, inside the actual fraction field. -/
theorem fraction_polynomial_iff_dvd (a p : TP) (ha : a ≠ 0) :
    (∃ r : TP, embed r=embed p/embed a) ↔ a ∣ p := by
  have ha' : embed a≠0 := by simpa only [map_zero] using (IsFractionRing.injective TP Frac).ne ha
  constructor
  · rintro ⟨r,hr⟩
    refine ⟨r,?_⟩
    have he := (eq_div_iff ha').mp hr
    apply IsFractionRing.injective TP Frac
    simpa only [map_mul,mul_comm] using he.symm
  · rintro ⟨r,rfl⟩
    exact ⟨r,by simp [map_mul,ha']⟩

/-- Restricting the numerator to a=0 recovers precisely the original binary polynomial. -/
theorem P_polynomial_iff (q : BP) :
    (∃ r : TP, embed r=P q (X 0) (X 1) (X 2)) ↔ q=0 := by
  rw [P,fraction_polynomial_iff_dvd _ _ (X_ne_zero 0)]
  constructor
  · rintro ⟨r,hr⟩
    let E : TP →ₐ[ℚ] BP := bind₁ ![0,X 0,X 1]
    have he : E (binaryLiftEval q (X 1) (X 2))=q := by
      have hv : (fun i : Fin 2 => E ((![X 1,X 2] : Fin 2 → TP) i))=X := by
        funext i
        fin_cases i <;> simp [E]
      dsimp only [E]
      simp only [binaryLiftEval,bind₁_bind₁]
      change bind₁ (fun i : Fin 2 => E ((![X 1,X 2] : Fin 2 → TP) i)) q=q
      rw [hv,bind₁_X_left,AlgHom.id_apply]
    have h := congrArg E hr
    rw [he,map_mul] at h
    simpa [E] using h
  · rintro rfl
    simp [binaryLiftEval]

end TernaryPoly.SymmetricOddRationalSeed
