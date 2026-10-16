module

public import TernaryPeriodPolynomials.SymmetricSolution.SeedData
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.PolynomialNorm

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.OrdinarySeedFibers
open OrdinaryCovectors OrdinaryCovectorOrbits OrdinaryPolynomialNorm

/-- The complete literal27-entry table; the zero row has value zero. -/
def seedValue (f P Q : TernaryPolynomial) (r : Covector) : TernaryPolynomial :=
  (![![![0, (substitute3 P (X 2) (X 0) (X 1)), -(substitute3 P (-X 2) (X 0) (X 1))],
      ![(substitute3 P (X 1) (X 0) (X 2)), (substitute3 Q (X 1) (X 2) (X 0)), -(substitute3 Q (X 1) (-X 2) (X 0))],
      ![-(substitute3 P (-X 1) (X 0) (X 2)), -(substitute3 Q (-X 1) (X 2) (X 0)), (substitute3 Q (-X 1) (-X 2) (X 0))]],
    ![![(substitute3 P (X 0) (X 1) (X 2)), (substitute3 Q (X 0) (X 2) (X 1)), -(substitute3 Q (X 0) (-X 2) (X 1))],
      ![(substitute3 Q (X 0) (X 1) (X 2)), (substitute3 f (X 0) (X 1) (X 2)), -(substitute3 f (X 0) (X 1) (-X 2))],
      ![-(substitute3 Q (X 0) (-X 1) (X 2)), -(substitute3 f (X 0) (-X 1) (X 2)), (substitute3 f (X 0) (-X 1) (-X 2))]],
    ![![-(substitute3 P (-X 0) (X 1) (X 2)), -(substitute3 Q (-X 0) (X 2) (X 1)), (substitute3 Q (-X 0) (-X 2) (X 1))],
      ![-(substitute3 Q (-X 0) (X 1) (X 2)), -(substitute3 f (-X 0) (X 1) (X 2)), (substitute3 f (-X 0) (X 1) (-X 2))],
      ![(substitute3 Q (-X 0) (-X 1) (X 2)), (substitute3 f (-X 0) (-X 1) (X 2)), -(substitute3 f (-X 0) (-X 1) (-X 2))]]] (r 0) (r 1) (r 2))

private theorem substitute_self (f : TernaryPolynomial) :
    substitute3 f (X 0) (X 1) (X 2)=f := by
  have hv : (![X 0,X 1,X 2] : Fin 3 → TernaryPolynomial)=X := by
    funext i
    fin_cases i <;> rfl
  simp [substitute3,hv]

theorem seedValue_one (f P Q : TernaryPolynomial) : seedValue f P Q ![1,0,0]=P := by
  exact substitute_self P

theorem seedValue_two (f P Q : TernaryPolynomial) : seedValue f P Q ![1,1,0]=Q := by
  exact substitute_self Q

theorem seedValue_three (f P Q : TernaryPolynomial) : seedValue f P Q ![1,1,1]=f := by
  exact substitute_self f

private theorem P_neg_second {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (a b c : TernaryPolynomial) : substitute3 P a (-b) c= -substitute3 P a b c := by
  have he := congrArg (fun t => substitute3 t a b c) h.p_odd_first
  change substitute3 (substitute3 P (X 0) (-X 1) (X 2)) a b c = substitute3 (-P) a b c at he
  rw [substitute3_substitute3] at he
  simpa [substitute3] using he

private theorem P_neg_third {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (a b c : TernaryPolynomial) : substitute3 P a b (-c)= -substitute3 P a b c := by
  have he := congrArg (fun t => substitute3 t a b c) h.p_odd_second
  change substitute3 (substitute3 P (X 0) (X 1) (-X 2)) a b c = substitute3 (-P) a b c at he
  rw [substitute3_substitute3] at he
  simpa [substitute3] using he

private theorem Q_neg_third {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (a b c : TernaryPolynomial) : substitute3 Q a b (-c)= -substitute3 Q a b c := by
  have he := congrArg (fun t => substitute3 t a b c) h.q_odd
  change substitute3 (substitute3 Q (X 0) (X 1) (-X 2)) a b c = substitute3 (-Q) a b c at he
  rw [substitute3_substitute3] at he
  simpa [substitute3] using he

private theorem D12_substitute (g a b c : TernaryPolynomial) :
    D12 (substitute3 g a b c)=substitute3 g (D12 a) (D12 b) (D12 c) := by
  exact substitute3_substitute3 g a b c (-X 0) (-X 1) (X 2)

private theorem D3_substitute (g a b c : TernaryPolynomial) :
    D3 (substitute3 g a b c)=substitute3 g (D3 a) (D3 b) (D3 c) := by
  exact substitute3_substitute3 g a b c (X 0) (X 1) (-X 2)

/-- All table entries obey the actual D12 coefficient symmetry. -/
theorem seedValue_sign12 {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (r : Covector) : seedValue f P Q (sign12 r)=D12 (seedValue f P Q r) := by
  have hr : r=![r 0,r 1,r 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hr]
  generalize r 0=a,r 1=b,r 2=c
  fin_cases a <;> fin_cases b <;> fin_cases c
  · change 0=(D12 (0))
    simp only [map_zero]
  · change (substitute3 P (X 2) (X 0) (X 1))=(D12 ((substitute3 P (X 2) (X 0) (X 1))))
    simp only [D12_substitute]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, P_neg_second h, P_neg_third h]
  · change -(substitute3 P (-X 2) (X 0) (X 1))=(D12 (-(substitute3 P (-X 2) (X 0) (X 1))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, P_neg_second h, P_neg_third h]
  · change -(substitute3 P (-X 1) (X 0) (X 2))=(D12 ((substitute3 P (X 1) (X 0) (X 2))))
    simp only [D12_substitute]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, P_neg_second h]
  · change -(substitute3 Q (-X 1) (X 2) (X 0))=(D12 ((substitute3 Q (X 1) (X 2) (X 0))))
    simp only [D12_substitute]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Q_neg_third h]
  · change (substitute3 Q (-X 1) (-X 2) (X 0))=(D12 (-(substitute3 Q (X 1) (-X 2) (X 0))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, Q_neg_third h]
  · change (substitute3 P (X 1) (X 0) (X 2))=(D12 (-(substitute3 P (-X 1) (X 0) (X 2))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, P_neg_second h]
  · change (substitute3 Q (X 1) (X 2) (X 0))=(D12 (-(substitute3 Q (-X 1) (X 2) (X 0))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, Q_neg_third h]
  · change -(substitute3 Q (X 1) (-X 2) (X 0))=(D12 ((substitute3 Q (-X 1) (-X 2) (X 0))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, Q_neg_third h]
  · change -(substitute3 P (-X 0) (X 1) (X 2))=(D12 ((substitute3 P (X 0) (X 1) (X 2))))
    simp only [D12_substitute]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, P_neg_second h]
  · change -(substitute3 Q (-X 0) (X 2) (X 1))=(D12 ((substitute3 Q (X 0) (X 2) (X 1))))
    simp only [D12_substitute]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Q_neg_third h]
  · change (substitute3 Q (-X 0) (-X 2) (X 1))=(D12 (-(substitute3 Q (X 0) (-X 2) (X 1))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, Q_neg_third h]
  · change (substitute3 Q (-X 0) (-X 1) (X 2))=(D12 ((substitute3 Q (X 0) (X 1) (X 2))))
    simp only [D12_substitute]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 f (-X 0) (-X 1) (X 2))=(D12 ((substitute3 f (X 0) (X 1) (X 2))))
    simp only [D12_substitute]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(substitute3 f (-X 0) (-X 1) (-X 2))=(D12 (-(substitute3 f (X 0) (X 1) (-X 2))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change -(substitute3 Q (-X 0) (X 1) (X 2))=(D12 (-(substitute3 Q (X 0) (-X 1) (X 2))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(substitute3 f (-X 0) (X 1) (X 2))=(D12 (-(substitute3 f (X 0) (-X 1) (X 2))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (substitute3 f (-X 0) (X 1) (-X 2))=(D12 ((substitute3 f (X 0) (-X 1) (-X 2))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (substitute3 P (X 0) (X 1) (X 2))=(D12 (-(substitute3 P (-X 0) (X 1) (X 2))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, P_neg_second h]
  · change (substitute3 Q (X 0) (X 2) (X 1))=(D12 (-(substitute3 Q (-X 0) (X 2) (X 1))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, Q_neg_third h]
  · change -(substitute3 Q (X 0) (-X 2) (X 1))=(D12 ((substitute3 Q (-X 0) (-X 2) (X 1))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, Q_neg_third h]
  · change -(substitute3 Q (X 0) (-X 1) (X 2))=(D12 (-(substitute3 Q (-X 0) (X 1) (X 2))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(substitute3 f (X 0) (-X 1) (X 2))=(D12 (-(substitute3 f (-X 0) (X 1) (X 2))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (substitute3 f (X 0) (-X 1) (-X 2))=(D12 ((substitute3 f (-X 0) (X 1) (-X 2))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (substitute3 Q (X 0) (X 1) (X 2))=(D12 ((substitute3 Q (-X 0) (-X 1) (X 2))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (substitute3 f (X 0) (X 1) (X 2))=(D12 ((substitute3 f (-X 0) (-X 1) (X 2))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(substitute3 f (X 0) (X 1) (-X 2))=(D12 (-(substitute3 f (-X 0) (-X 1) (-X 2))))
    simp only [D12_substitute, map_neg]
    simp only [D12, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]

/-- All table entries obey the determinant sign in the actual D3 coefficient symmetry. -/
theorem seedValue_sign3 {f P Q : TernaryPolynomial} (h : SymmetricSeedData f P Q)
    (r : Covector) : seedValue f P Q (sign3 r)= -D3 (seedValue f P Q r) := by
  have hr : r=![r 0,r 1,r 2] := by
    funext i
    fin_cases i <;> rfl
  rw [hr]
  generalize r 0=a,r 1=b,r 2=c
  fin_cases a <;> fin_cases b <;> fin_cases c
  · change 0=-(D3 (0))
    simp only [map_zero,neg_zero]
  · change -(substitute3 P (-X 2) (X 0) (X 1))=-(D3 ((substitute3 P (X 2) (X 0) (X 1))))
    simp only [D3_substitute]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 P (X 2) (X 0) (X 1))=-(D3 (-(substitute3 P (-X 2) (X 0) (X 1))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (substitute3 P (X 1) (X 0) (X 2))=-(D3 ((substitute3 P (X 1) (X 0) (X 2))))
    simp only [D3_substitute]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, P_neg_third h]
  · change -(substitute3 Q (X 1) (-X 2) (X 0))=-(D3 ((substitute3 Q (X 1) (X 2) (X 0))))
    simp only [D3_substitute]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 Q (X 1) (X 2) (X 0))=-(D3 (-(substitute3 Q (X 1) (-X 2) (X 0))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(substitute3 P (-X 1) (X 0) (X 2))=-(D3 (-(substitute3 P (-X 1) (X 0) (X 2))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, P_neg_third h]
  · change (substitute3 Q (-X 1) (-X 2) (X 0))=-(D3 (-(substitute3 Q (-X 1) (X 2) (X 0))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(substitute3 Q (-X 1) (X 2) (X 0))=-(D3 ((substitute3 Q (-X 1) (-X 2) (X 0))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (substitute3 P (X 0) (X 1) (X 2))=-(D3 ((substitute3 P (X 0) (X 1) (X 2))))
    simp only [D3_substitute]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, P_neg_third h]
  · change -(substitute3 Q (X 0) (-X 2) (X 1))=-(D3 ((substitute3 Q (X 0) (X 2) (X 1))))
    simp only [D3_substitute]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 Q (X 0) (X 2) (X 1))=-(D3 (-(substitute3 Q (X 0) (-X 2) (X 1))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (substitute3 Q (X 0) (X 1) (X 2))=-(D3 ((substitute3 Q (X 0) (X 1) (X 2))))
    simp only [D3_substitute]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, Q_neg_third h]
  · change -(substitute3 f (X 0) (X 1) (-X 2))=-(D3 ((substitute3 f (X 0) (X 1) (X 2))))
    simp only [D3_substitute]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 f (X 0) (X 1) (X 2))=-(D3 (-(substitute3 f (X 0) (X 1) (-X 2))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(substitute3 Q (X 0) (-X 1) (X 2))=-(D3 (-(substitute3 Q (X 0) (-X 1) (X 2))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, Q_neg_third h]
  · change (substitute3 f (X 0) (-X 1) (-X 2))=-(D3 (-(substitute3 f (X 0) (-X 1) (X 2))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(substitute3 f (X 0) (-X 1) (X 2))=-(D3 ((substitute3 f (X 0) (-X 1) (-X 2))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(substitute3 P (-X 0) (X 1) (X 2))=-(D3 (-(substitute3 P (-X 0) (X 1) (X 2))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, P_neg_third h]
  · change (substitute3 Q (-X 0) (-X 2) (X 1))=-(D3 (-(substitute3 Q (-X 0) (X 2) (X 1))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(substitute3 Q (-X 0) (X 2) (X 1))=-(D3 ((substitute3 Q (-X 0) (-X 2) (X 1))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(substitute3 Q (-X 0) (X 1) (X 2))=-(D3 (-(substitute3 Q (-X 0) (X 1) (X 2))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, Q_neg_third h]
  · change (substitute3 f (-X 0) (X 1) (-X 2))=-(D3 (-(substitute3 f (-X 0) (X 1) (X 2))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change -(substitute3 f (-X 0) (X 1) (X 2))=-(D3 ((substitute3 f (-X 0) (X 1) (-X 2))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]
  · change (substitute3 Q (-X 0) (-X 1) (X 2))=-(D3 ((substitute3 Q (-X 0) (-X 1) (X 2))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg, Q_neg_third h]
  · change -(substitute3 f (-X 0) (-X 1) (-X 2))=-(D3 ((substitute3 f (-X 0) (-X 1) (X 2))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · change (substitute3 f (-X 0) (-X 1) (X 2))=-(D3 (-(substitute3 f (-X 0) (-X 1) (-X 2))))
    simp only [D3_substitute, map_neg]
    simp only [D3, bind₁_X_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, neg_neg]

end TernaryPoly.OrdinarySeedFibers
