module

public import TernaryPeriodPolynomials.SymmetricSolution.RationalTrace.SinglePole
public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.CoordinateActions

@[expose] public section

open MvPolynomial
noncomputable section
namespace TernaryPoly.SymmetricRationalTrace
open SymmetricOddRationalSeed SymmetricOddRationalTower OrdinaryRationalFiber
open SinglePoleSupport SinglePoleCoordinate PolynomialGLAction

/-- The coordinate-sign matrix corresponds to precisely this set of flipped coordinates. -/
def signSet (s : Fin 3 → Bool) : Finset (Fin 3) := Finset.univ.filter fun i => s i

theorem oddSign_eq (s : Fin 3 → Bool) : oddSign s=(-1 : ℚ)^(signSet s).card := by
  simp [oddSign,signEntry,signSet,Finset.prod_ite]

/-- The actual integral permutation acts by inverse-indexed fracPerm. -/
theorem fractionEquiv_permutation (π : Equiv.Perm (Fin 3)) (x : Frac) :
    SinglePole.fractionEquiv (integralRational (permutationMatrix π)) x=fracPerm π⁻¹ x := by
  have he : (SinglePole.fractionEquiv (integralRational (permutationMatrix π))).toRingHom=
      (fracPerm π⁻¹).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := TP)
    intro p
    change SinglePole.fractionEquiv (integralRational (permutationMatrix π)) (embed p)=
      fracPerm π⁻¹ (embed p)
    rw [SinglePole.fractionEquiv_embed,fracPerm_embed,substitute_permutation]
    apply congrArg embed
    have hp : (rename π : TP →ₐ[ℚ] TP)=OrdinaryFiberPermutations.permutePoly π⁻¹ := by
      apply MvPolynomial.algHom_ext
      intro i
      simp [OrdinaryFiberPermutations.permutePoly]
      rfl
    exact DFunLike.congr_fun hp p
  exact DFunLike.congr_fun he x

/-- The actual integral sign action is the same fraction-field substitution used in the trace. -/
theorem fractionEquiv_sign (s : Fin 3 → Bool) (x : Frac) :
    SinglePole.fractionEquiv (integralRational (signMatrix s)) x=fracSign (signSet s) x := by
  have he : (SinglePole.fractionEquiv (integralRational (signMatrix s))).toRingHom=
      (fracSign (signSet s)).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := TP)
    intro p
    change SinglePole.fractionEquiv (integralRational (signMatrix s)) (embed p)=
      fracSign (signSet s) (embed p)
    rw [SinglePole.fractionEquiv_embed,fracSign_embed,substitute_sign]
    congr 2
    simp [OrdinarySignedFibers.signPoly,signSet]
  exact DFunLike.congr_fun he x

theorem trace_fraction_sign {k : ℕ} (f : TP) (q : Fin k → BP) (hq)
    (hc : C f=f) (hs : S f=f) (s : Fin 3 → Bool) :
    SinglePole.fractionEquiv (integralRational (signMatrix s)) (trace f q hq)=
      oddSign s • trace f q hq := by
  rw [fractionEquiv_sign,oddSign_eq]
  have he := trace_sign f q hq hc hs (signSet s)
  have hc2 : (-1 : ℚ)^(signSet s).card*(-1 : ℚ)^(signSet s).card=1 := by
    rw [←mul_pow]
    norm_num
  have he' := congrArg (fun x : Frac => (-1 : ℚ)^(signSet s).card • x) he
  rw [smul_smul,hc2,one_smul] at he'
  exact he'

/-- The determinant-one norm matrix has trivial determinant character at every exponent. -/
theorem normMatrix_character (e : ℤ) :
    determinantCharacter e (ReferenceCoefficientMatrices.rational ReferenceCoefficientMatrices.a)=1 := by
  have hd : Matrix.GeneralLinearGroup.det
      (ReferenceCoefficientMatrices.rational ReferenceCoefficientMatrices.a)=1 := by
    rw [Matrix.GeneralLinearGroup.map_det,ReferenceCoefficientMatrices.det_a,map_one]
  change ((Matrix.GeneralLinearGroup.det
    (ReferenceCoefficientMatrices.rational ReferenceCoefficientMatrices.a) : ℚˣ) : ℚ)^e=1
  rw [hd]
  simp

theorem fractionAction_normMatrix (e : ℤ) (x : Frac) :
    SinglePole.fractionAction e (ReferenceCoefficientMatrices.rational ReferenceCoefficientMatrices.a) x=
      fracA2 x := by
  rw [SinglePole.fractionAction_apply,normMatrix_character,one_smul,fractionEquiv_a]

theorem fractionAction_normMatrix_sq (e : ℤ) (x : Frac) :
    SinglePole.fractionAction e
      (ReferenceCoefficientMatrices.rational (ReferenceCoefficientMatrices.a^2)) x=fracA x := by
  rw [map_pow,pow_two,map_mul,Module.End.mul_apply,fractionAction_normMatrix,fractionAction_normMatrix]
  change fracA (fracA (fracA (fracA x)))=fracA x
  rw [fracA_cube]

variable {n k : ℕ}

/-- All actual integral permutation equations for the homogeneous trace, at every determinant twist. -/
theorem homogeneousTrace_permutation (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    (hc : C f=f) (hs : S f=f) (e : ℤ) (π : Equiv.Perm (Fin 3)) :
    integralSinglePoleAction n e (permutationMatrix π) (homogeneousTrace f hf q hq hd)=
      determinantCharacter e (integralRational (permutationMatrix π)) • homogeneousTrace f hf q hq hd := by
  apply Subtype.ext
  change SinglePole.fractionAction e (integralRational (permutationMatrix π)) (trace f q hq)=
    determinantCharacter e (integralRational (permutationMatrix π)) • trace f q hq
  rw [SinglePole.fractionAction_apply,fractionEquiv_permutation,trace_permutation f q hq hc hs]

/-- All actual independent integral sign equations for the homogeneous trace. -/
theorem homogeneousTrace_sign (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    (hc : C f=f) (hs : S f=f) (e : ℤ) (s : Fin 3 → Bool) :
    integralSinglePoleAction n e (signMatrix s) (homogeneousTrace f hf q hq hd)=
      (determinantCharacter e (integralRational (signMatrix s))*oddSign s) •
        homogeneousTrace f hf q hq hd := by
  apply Subtype.ext
  change SinglePole.fractionAction e (integralRational (signMatrix s)) (trace f q hq)=
    (determinantCharacter e (integralRational (signMatrix s))*oddSign s) • trace f q hq
  rw [SinglePole.fractionAction_apply,trace_fraction_sign f q hq hc hs,mul_smul]

/-- The actual a/a² norm in the homogeneous single-pole module vanishes. -/
theorem homogeneousTrace_norm (f : TP) (hf : f.IsHomogeneous n)
    (q : Fin k → BP) (hq : ∀ i,SymmetricBinaryPeriodRelations (q i))
    (hd : ∀ i,(q i).IsHomogeneous (n+1-2*(i:ℕ)))
    (l : Fin k → TP) (hl : ∀ i,binaryPeriodLift (q i)=(X 0+X 1+X 2)*l i)
    (he : f=∑ i : Fin k,(X 0+X 1+X 2)^(2*(i:ℕ))*l i)
    (hr : PeriodRelations f) (hs : S f=f) (e : ℤ) :
    homogeneousTrace f hf q hq hd+
      integralSinglePoleAction n e ReferenceCoefficientMatrices.a (homogeneousTrace f hf q hq hd)+
      integralSinglePoleAction n e (ReferenceCoefficientMatrices.a^2) (homogeneousTrace f hf q hq hd)=0 := by
  apply Subtype.ext
  change trace f q hq+
    SinglePole.fractionAction e (ReferenceCoefficientMatrices.rational ReferenceCoefficientMatrices.a) (trace f q hq)+
    SinglePole.fractionAction e (ReferenceCoefficientMatrices.rational (ReferenceCoefficientMatrices.a^2)) (trace f q hq)=0
  rw [fractionAction_normMatrix,fractionAction_normMatrix_sq]
  linear_combination trace_norm q hq l hl f he hr hs

end TernaryPoly.SymmetricRationalTrace
