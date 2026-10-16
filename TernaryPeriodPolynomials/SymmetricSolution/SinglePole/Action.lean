module

public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Scaling

@[expose] public section


open MvPolynomial Matrix
noncomputable section
namespace TernaryPoly.SinglePole
open PolynomialGLAction
open ModThreeGoodAction AugmentedFrameComplex PrimitiveLineHeight
attribute [local instance] Classical.propDecidable

/-- Inverse substitution as an algebra automorphism of the actual polynomial ring. -/
def polynomialEquiv (g : GL3) : Poly ≃ₐ[ℚ] Poly :=
  AlgEquiv.ofAlgHom (substitute (g⁻¹ : GL3)) (substitute (g : GL3))
    (by rw [substitute_comp, ← GeneralLinearGroup.coe_mul, mul_inv_cancel,
            GeneralLinearGroup.coe_one, substitute_one])
    (by rw [substitute_comp, ← GeneralLinearGroup.coe_mul, inv_mul_cancel,
            GeneralLinearGroup.coe_one, substitute_one])

@[simp] theorem polynomialEquiv_apply (g : GL3) (p : Poly) :
    polynomialEquiv g p = substitute (g⁻¹ : GL3) p := rfl

/-- Extension of inverse substitution to the actual rational function field. -/
def fractionEquiv (g : GL3) : Frac ≃ₐ[ℚ] Frac :=
  IsFractionRing.algEquivOfAlgEquiv (polynomialEquiv g)

@[simp] theorem fractionEquiv_embed (g : GL3) (p : Poly) :
    fractionEquiv g (embed p) = embed (substitute (g⁻¹ : GL3) p) :=
  IsFractionRing.algEquivOfAlgEquiv_algebraMap _ p

/-- The extension obeys the genuine left representation law. -/
def fractionUntwisted : Representation ℚ GL3 Frac where
  toFun g := (fractionEquiv g).toLinearMap
  map_one' := by
    have h : (fractionEquiv (1 : GL3)).toRingHom = RingHom.id Frac := by
      apply IsFractionRing.ringHom_ext (A := Poly)
      intro p
      simp [fractionEquiv_embed, substitute_one]
    ext x
    exact RingHom.congr_fun h x
  map_mul' g h := by
    have he : (fractionEquiv (g*h)).toRingHom =
        (fractionEquiv g).toRingHom.comp (fractionEquiv h).toRingHom := by
      apply IsFractionRing.ringHom_ext (A := Poly)
      intro p
      change fractionEquiv (g*h) (embed p) = fractionEquiv g (fractionEquiv h (embed p))
      rw [fractionEquiv_embed,fractionEquiv_embed,fractionEquiv_embed]
      apply congrArg embed
      exact congrArg (fun f : Poly →ₐ[ℚ] Poly => f p)
        (by simpa only [_root_.mul_inv_rev, GeneralLinearGroup.coe_mul] using
          (substitute_comp (g⁻¹ : GL3) (h⁻¹ : GL3)).symm)
    ext x
    exact RingHom.congr_fun he x

/-- The determinant exponent is explicit; e=-1 is the scalar convention in the paper. -/
def fractionAction (e : ℤ) : Representation ℚ GL3 Frac where
  toFun g :=
    { toFun x := determinantCharacter e g • fractionUntwisted g x
      map_add' x y := by
        rw [map_add]
        exact (inferInstance : Module ℚ Frac).toDistribMulAction.smul_add
          (determinantCharacter e g) (fractionUntwisted g x) (fractionUntwisted g y)
      map_smul' c x := by rw [map_smul,smul_comm]; rfl }
  map_one' := by
    ext x
    change determinantCharacter e (1 : GL3) • fractionUntwisted (1 : GL3) x = x
    rw [map_one,map_one,Module.End.one_apply,one_smul]
  map_mul' g h := by
    ext x
    change determinantCharacter e (g*h) • fractionUntwisted (g*h) x =
      determinantCharacter e g • fractionUntwisted g (determinantCharacter e h • fractionUntwisted h x)
    rw [map_mul,map_mul,Module.End.mul_apply,map_smul,smul_smul]

theorem fractionAction_apply (e : ℤ) (g : GL3) (x : Frac) :
    fractionAction e g x = determinantCharacter e g • fractionEquiv g x := rfl

@[simp] theorem fractionAction_embed (e : ℤ) (g : GL3) (p : Poly) :
    fractionAction e g (embed p) = embed (action e g p) := by
  change determinantCharacter e g • fractionEquiv g (embed p) = _
  rw [fractionEquiv_embed,action_apply]
  exact ((IsScalarTower.toAlgHom ℚ Poly Frac).toLinearMap.map_smul _ _).symm

/-- Substitution of a linear form is literal right multiplication of its normal row. -/
theorem substitute_form (M : Matrix (Fin 3) (Fin 3) ℚ) (v : Space) :
    substitute M (form v) = form (vecMul v M) := by
  simp only [form, substitute, map_sum, map_mul, bind₁_C_right, bind₁_X_right,
    linearForm, vecMul, dotProduct, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Invertibility ensures a nonzero rational normal remains nonzero. -/
theorem vecMul_inv_ne_zero (g : GL3) (v : Space) (hv : v ≠ 0) :
    vecMul v (↑(g⁻¹) : Matrix (Fin 3) (Fin 3) ℚ) ≠ 0 := by
  intro h
  have he := congrArg (fun w : Space => vecMul w (↑g : Matrix (Fin 3) (Fin 3) ℚ)) h
  rw [vecMul_vecMul, ← GeneralLinearGroup.coe_mul, inv_mul_cancel,
    GeneralLinearGroup.coe_one, vecMul_one, zero_vecMul] at he
  exact hv he

/-- Every single-pole finite presentation remains a single-pole finite presentation. -/
theorem fractionUntwisted_mem (n : ℕ) (g : GL3) (x : Frac)
    (hx : x ∈ singlePole n) : fractionUntwisted g x ∈ singlePole n := by
  obtain ⟨p,t,rfl⟩ := (mem_singlePole_iff n x).mp hx
  change fractionEquiv g _ ∈ _
  rw [map_add,map_sum,fractionEquiv_embed]
  apply (singlePole n).add_mem
  · simpa only [polynomialInclusion_val] using
      (polynomialInclusion n ⟨_,substitute_homogeneous _ p.property⟩).property
  · apply (singlePole n).sum_mem
    intro H _
    rw [map_div₀,fractionEquiv_embed,fractionEquiv_embed]
    change embed _ / embed (substitute (g⁻¹ : GL3)
      (form (rationalVector (primitiveGenerator H)))) ∈ _
    rw [substitute_form]
    exact fraction_mem_singlePole n _
      (vecMul_inv_ne_zero g _ (primitiveGenerator_ne_zero H))
      ⟨_,substitute_homogeneous _ (t H).property⟩

/-- The actual single-pole subspace is invariant, with the stated determinant convention. -/
theorem fractionAction_mem (n : ℕ) (e : ℤ) (g : GL3) (x : Frac)
    (hx : x ∈ singlePole n) : fractionAction e g x ∈ singlePole n := by
  change determinantCharacter e g • fractionUntwisted g x ∈ _
  exact (singlePole n).smul_mem _ (fractionUntwisted_mem n g x hx)

/-- Genuine coefficient action on M_n, inherited from the actual fraction field. -/
def singlePoleAction (n : ℕ) (e : ℤ) : Representation ℚ GL3 (singlePole n) :=
  (fractionAction e).subrepresentation (singlePole n) (fractionAction_mem n e)

@[simp] theorem singlePoleAction_val (n : ℕ) (e : ℤ) (g : GL3) (x : singlePole n) :
    (singlePoleAction n e g x).val = fractionAction e g x.val := rfl

/-- The polynomial injection intertwines the actual homogeneous action. -/
theorem polynomialInclusion_equivariant (n : ℕ) (e : ℤ) (g : GL3) (p : V n) :
    singlePoleAction n e g (polynomialInclusion n p) =
      polynomialInclusion n (homogeneousAction n e g p) := by
  apply Subtype.ext
  simp only [singlePoleAction_val,polynomialInclusion_val,fractionAction_embed,
    homogeneousAction_coe]

end TernaryPoly.SinglePole
