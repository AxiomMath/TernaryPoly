module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Rational.FiberEquivariance

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinaryRationalFiber
open SymmetricOddRationalSeed SymmetricOddRationalTower
open OrdinaryCovectors OrdinaryCovectorOrbits

/-- Rational linearity is canonical even when fraction-field algebra instances differ. -/
def linearAction (e : Frac ≃ₐ[ℚ] Frac) : Frac →ₗ[ℚ] Frac where
  toFun := e
  map_add' := map_add e
  map_smul' := map_rat_smul e

/-- The actual three-term norm on rational residue fibers. -/
def fiberNorm (F : Covector → Frac) (r : Covector) : Frac :=
  F r+fracA (F (stepA (stepA r)))+fracA2 (F (stepA r))

theorem fiberNorm_eq (F : Covector → Frac) (r : Covector) :
    fiberNorm F r=OrdinaryFiberNorm.norm (linearAction fracA) F r := rfl

/-- The existing exact orbit exhaustion applies to the actual fraction-field coefficient maps. -/
theorem all_norms_of_five (F : Covector → Frac)
    (h12 : ∀ r,F (sign12 r)=fracD12 (F r))
    (h3 : ∀ r,F (sign3 r)= -fracD3 (F r))
    (hfive : ∀ i,fiberNorm F (representative i)=0) :
    ∀ r : Covector,r≠0 → fiberNorm F r=0 := by
  intro r hr
  rw [fiberNorm_eq]
  apply OrdinaryFiberNorm.all_norms_of_five (linearAction fracA) (linearAction fracD12)
    (-(linearAction fracD3)) F fracA_cube h12 h3 fracA_D12 ?_ ?_ r hr
  · intro f
    change fracA (-fracD3 f)= -fracD3 (fracA f)
    rw [map_neg,fracA_D3]
  · intro i
    rw [←fiberNorm_eq]
    exact hfive i

variable {k : ℕ}

/-- The matching Q obeys the first mixed equation in arbitrary polynomial coordinates,
inside the actual fraction field. -/
theorem qValue_mixed (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (f : TP) (hf : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (a b c : TP) : qValue q hq a b (c+a)-qValue q hq a b c=fValue f (a+c) (-c) b := by
  have hm := qPolynomial_first_mixed q hq l hl
  rw [←hf] at hm
  have he : substitute3 (substitute3 (qPolynomial q hq) (X 0) (X 1) (X 2+X 0)) a b c-
      substitute3 (qPolynomial q hq) a b c =
      substitute3 (substitute3 f (X 0+X 2) (-X 2) (X 1)) a b c := by
    simpa only [substitute3,map_sub] using congrArg (fun p => substitute3 p a b c) hm
  rw [substitute3_substitute3,substitute3_substitute3] at he
  have hp : substitute3 (qPolynomial q hq) a b (c+a)-substitute3 (qPolynomial q hq) a b c =
      substitute3 f (a+c) (-c) b := by
    simpa [substitute3] using he
  change embed _-embed _=embed _
  rw [←map_sub,hp]

/-- All five literal rational seed norms follow from the actual tower equations. -/
theorem five_seed_norms (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (f : TP) (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hf : N f=0) (hQ : N (qPolynomial q hq)=0) (i : Fin 5) :
    fiberNorm (seedValue f q hq) (representative i)=0 := by
  fin_cases i
  · change pValue q (X 2) (X 0) (X 1)+
      fracA (pValue q (X 2) (X 0) (X 1))+
      fracA2 (pValue q (X 2) (X 0) (X 1))=0
    rw [fracA_P,fracA2_P]
    simpa only [A,A2,bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using pValue_norm q hq (X 2) (X 0) (X 1)
  · change seedValue f q hq ![1,1,0]+fracA (seedValue f q hq ![1,1,0])+
      fracA2 (seedValue f q hq ![1,1,0])=0
    rw [seedValue_two,fracA_embed,fracA2_embed,←map_add,←map_add]
    exact (congrArg embed hQ).trans (map_zero _)
  · change seedValue f q hq ![1,1,1]+fracA (seedValue f q hq ![1,1,1])+
      fracA2 (seedValue f q hq ![1,1,1])=0
    rw [seedValue_three,fracA_embed,fracA2_embed,←map_add,←map_add]
    exact (congrArg embed hf).trans (map_zero _)
  · change qValue q hq (X 0) (X 2) (X 1)+
      fracA (-fValue f (-X 0) (X 1) (X 2))+
      fracA2 (-qValue q hq (-X 1) (X 2) (X 0))=0
    rw [map_neg,map_neg,fracA_F,fracA2_Q]
    simp only [A,A2,bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,map_neg,neg_neg]
    have hm := qValue_mixed q hq l hl f he (X 0) (X 2) (X 1-X 0)
    have ha : X 1-X 0+X 0=(X 1 : TP) := by ring
    have hb : X 0+(X 1-X 0)=(X 1 : TP) := by ring
    have hc : -(X 1-X 0)=(X 0-X 1 : TP) := by ring
    rw [ha,hb,hc] at hm
    linear_combination hm
  · change pValue q (X 0) (X 1) (X 2)+
      fracA (-qValue q hq (-X 0) (X 1) (X 2))+
      fracA2 (-pValue q (-X 1) (X 0) (X 2))=0
    rw [map_neg,map_neg,fracA_Q,fracA2_P]
    simp only [A,A2,bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,map_neg,neg_neg]
    have hm := pValue_mixed q hq (X 0) (X 2) (X 1-X 0) (X_ne_zero 0)
    have ha : X 1-X 0+X 0=(X 1 : TP) := by ring
    have hb : X 0+(X 1-X 0)=(X 1 : TP) := by ring
    have hc : -(X 1-X 0)=(X 0-X 1 : TP) := by ring
    rw [ha,hb,hc] at hm
    change pValue q (X 0) (X 1) (X 2)-pValue q (X 0) (X 1-X 0) (X 2)=
      qValue q hq (X 0-X 1) (X 1) (X 2) at hm
    rw [qValue_swap q hq (X 1) (X 0-X 1) (X 2)] at hm
    linear_combination hm

/-- The full actual26-fiber norm system of every finite odd rational tower. -/
theorem seedValue_all_norms (q : Fin k → BP) (hq : ∀ i, SymmetricBinaryPeriodRelations (q i))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (f : TP) (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hf : PeriodRelations f) (hs : S f=f) :
    ∀ r : Covector,r≠0 → fiberNorm (seedValue f q hq) r=0 :=
  all_norms_of_five (seedValue f q hq) (seedValue_sign12 f q hq) (seedValue_sign3 f q hq)
    (five_seed_norms q hq l hl f he hf.2 (qPolynomial_norm q hq l hl f he hf hs))

end TernaryPoly.OrdinaryRationalFiber
