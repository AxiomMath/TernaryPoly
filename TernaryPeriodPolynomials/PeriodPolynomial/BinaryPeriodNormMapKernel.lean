module

public import TernaryPeriodPolynomials.PeriodPolynomial.BinaryPeriodNormMap

@[expose] public section


open MvPolynomial
noncomputable section
namespace TernaryPoly.BinaryFiniteInvariant

private theorem bind_comp (q a b c e : MvPolynomial (Fin 2) ℚ) :
    bind₁ ![a,b] (bind₁ ![c,e] q) = bind₁ ![bind₁ ![a,b] c,bind₁ ![a,b] e] q := by
  rw [bind₁_bind₁]
  congr 2
  funext i
  fin_cases i <;> rfl

private theorem swap_eval (q : MvPolynomial (Fin 2) ℚ) (hs : bind₁ ![X 1,X 0] q=q)
    (a b : MvPolynomial (Fin 2) ℚ) : bind₁ ![b,a] q=bind₁ ![a,b] q := by
  have h := congrArg (bind₁ ![a,b]) hs
  simpa only [bind_comp,bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one] using h

private theorem neg_first_eval (q : MvPolynomial (Fin 2) ℚ) (hd : bind₁ ![-X 0,X 1] q=-q)
    (a b : MvPolynomial (Fin 2) ℚ) : bind₁ ![-a,b] q=-bind₁ ![a,b] q := by
  have h := congrArg (bind₁ ![a,b]) hd
  simpa only [bind_comp,map_neg,bind₁_X_right,Matrix.cons_val_zero,Matrix.cons_val_one] using h

private theorem neg_second_eval (q : MvPolynomial (Fin 2) ℚ)
    (hs : bind₁ ![X 1,X 0] q=q) (hd : bind₁ ![-X 0,X 1] q=-q)
    (a b : MvPolynomial (Fin 2) ℚ) : bind₁ ![a,-b] q=-bind₁ ![a,b] q := by
  rw [swap_eval q hs (-b) a,neg_first_eval q hd b a,swap_eval q hs a b]

theorem rotation_sq_coe (d : ℕ) (q : H d) :
    (rotation d (rotation d q)).val = bind₁ ![X 1-X 0,-X 0] q.val := by
  rw [rotation_coe,rotation_coe,bind_comp]
  congr 2
  ext i
  fin_cases i <;> simp
  ring

/-- The norm restriction is the literal three-term period operator, with its exact signs. -/
theorem norm_coe_of_oddSymmetric (d : ℕ) (q : oddSymmetric d) :
    (norm d q.val).val = q.val.val - bind₁ ![X 0-X 1,X 1] q.val.val +
      bind₁ ![X 0,X 0-X 1] q.val.val := by
  have hs : bind₁ ![X 1,X 0] q.val.val=q.val.val := by
    simpa only [swap_coe] using congrArg Subtype.val q.property.1
  have hd : bind₁ ![-X 0,X 1] q.val.val=-q.val.val := by
    simpa only [negateFirst_coe,Submodule.coe_neg] using congrArg Subtype.val q.property.2
  change q.val.val + (rotation d q.val).val + (rotation d (rotation d q.val)).val = _
  rw [rotation_sq_coe,rotation_coe]
  rw [neg_first_eval _ hd,swap_eval _ hs (X 0-X 1) (X 1),
    show (X 1-X 0 : MvPolynomial (Fin 2) ℚ) = -(X 0-X 1) by ring,
    neg_first_eval _ hd,neg_second_eval _ hs hd,neg_neg,
    swap_eval _ hs (X 0) (X 0-X 1)]
  simp only [sub_eq_add_neg]

/-- Vanishing of the actual restricted norm is exactly the existing four period equations. -/
theorem normMap_zero_iff (d : ℕ) (q : oddSymmetric d) :
    normMap d q=0 ↔ SymmetricBinaryPeriodRelations q.val.val := by
  have hs : bind₁ ![X 1,X 0] q.val.val=q.val.val := by
    simpa only [swap_coe] using congrArg Subtype.val q.property.1
  have hd : bind₁ ![-X 0,X 1] q.val.val=-q.val.val := by
    simpa only [negateFirst_coe,Submodule.coe_neg] using congrArg Subtype.val q.property.2
  constructor
  · intro hz
    refine ⟨hs,hd,?_,?_⟩
    · have hx : (![X 0,X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ)=X := by
        funext i
        fin_cases i <;> rfl
      simpa only [hx,bind₁_X_left,AlgHom.id_apply] using neg_second_eval _ hs hd (X 0) (X 1)
    · have he := congrArg (fun x : invariants d => x.val.val) hz
      simpa only [normMap_val,norm_coe_of_oddSymmetric,Submodule.coe_zero] using he
  · intro hq
    apply Subtype.ext
    apply Subtype.ext
    change (norm d q.val).val=0
    rw [norm_coe_of_oddSymmetric]
    exact hq.period

/-- The kernel has a literal identity-on-polynomials equivalence with the original period space. -/
def kernelEquiv (d : ℕ) : (normMap d).ker ≃ₗ[ℚ] OrdinaryResiduePeriod.periodSpace d where
  toFun q := ⟨q.val.val,(normMap_zero_iff d q.val).mp q.property⟩
  invFun q := ⟨⟨q.val,by
    constructor
    · apply Subtype.ext
      rw [swap_coe]
      exact q.property.swap
    · apply Subtype.ext
      rw [negateFirst_coe]
      exact q.property.odd_first⟩,(normMap_zero_iff d _).mpr q.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end TernaryPoly.BinaryFiniteInvariant
