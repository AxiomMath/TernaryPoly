module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.UpperPowers

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

def radicalFunctionRepresentation (n : ℕ) :
    Representation ℂ (Multiplicative ℤ) (ℤ × ℤ → HomogeneousPoly n) where
  toFun k :=
    { toFun := fun values x => rationalCoefficientComponent n trivialCharacter
        (upperTranslationAt k.toAdd) (values (shearPair k.toAdd x))
      map_add' := by
        intro a b
        funext x
        exact map_add _ _ _
      map_smul' := by
        intro r a
        funext x
        change rationalCoefficientComponent n trivialCharacter (upperTranslationAt k.toAdd)
          (r • a (shearPair k.toAdd x)) = r •
          rationalCoefficientComponent n trivialCharacter (upperTranslationAt k.toAdd)
            (a (shearPair k.toAdd x))
        exact map_smul (rationalCoefficientComponent n trivialCharacter (upperTranslationAt k.toAdd))
          r (a (shearPair k.toAdd x)) }
  map_one' := by
    apply LinearMap.ext
    intro values
    funext x
    change rationalCoefficientComponent n trivialCharacter (upperTranslationAt 0)
      (values (shearPair 0 x)) = values x
    rw [upperTranslationAt_zero,shearPair_zero,map_one,Module.End.one_apply]
  map_mul' k l := by
    apply LinearMap.ext
    intro values
    funext x
    change rationalCoefficientComponent n trivialCharacter (upperTranslationAt (k.toAdd+l.toAdd))
        (values (shearPair (k.toAdd+l.toAdd) x)) =
      rationalCoefficientComponent n trivialCharacter (upperTranslationAt k.toAdd)
        (rationalCoefficientComponent n trivialCharacter (upperTranslationAt l.toAdd)
          (values (shearPair l.toAdd (shearPair k.toAdd x))))
    rw [upperTranslationAt_add,shearPair_add,map_mul,Module.End.mul_apply]

def radicalBoundary (n : ℕ) : HomogeneousPoly n →ₗ[ℂ] (ℤ × ℤ → HomogeneousPoly n) where
  toFun p x := p-rationalCoefficientComponent n trivialCharacter
    (integralRadicalHom (Multiplicative.ofAdd x)) p
  map_add' p q := by
    funext x
    simp only [map_add,Pi.add_apply]
    abel
  map_smul' r p := by
    funext x
    simp only [map_smul,smul_sub,Pi.smul_apply,RingHom.id_apply]

theorem radicalBoundary_equivariant (n : ℕ) (k : ℤ) (p : HomogeneousPoly n) :
    radicalBoundary n (rationalCoefficientComponent n trivialCharacter (upperTranslationAt k) p) =
      radicalFunctionRepresentation n (Multiplicative.ofAdd k) (radicalBoundary n p) := by
  funext x
  change _ = rationalCoefficientComponent n trivialCharacter (upperTranslationAt k)
    (p-rationalCoefficientComponent n trivialCharacter
      (integralRadicalHom (Multiplicative.ofAdd (shearPair k x))) p)
  rw [← upperTranslationAt_radical_conjugate,representation_coboundary_conjugate]
  rfl

def cyclicMixedValue (n : ℕ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (k : ℤ) (x : ℤ × ℤ) : HomogeneousPoly n :=
  mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c (upperTranslationAt k)
    (integralRadicalHom (Multiplicative.ofAdd x))

theorem cyclicMixedValue_cocycle (n : ℕ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (pure : PureMixedBadLine c) (k l : ℤ) :
    cyclicMixedValue n c (k+l) = cyclicMixedValue n c k+
      radicalFunctionRepresentation n (Multiplicative.ofAdd k) (cyclicMixedValue n c l) := by
  funext x
  change mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c
      (upperTranslationAt (k+l)) (integralRadicalHom (Multiplicative.ofAdd x)) = _
  rw [upperTranslationAt_add,mixedValue_levi_cocycle rationalLevel
    (rationalCoefficientComponent n trivialCharacter) c
    ⟨upperTranslationAt k,upperTranslationAt_mem k⟩
    ⟨integralRadicalHom (Multiplicative.ofAdd x),rationalLevel_lineUnipotent x.1 x.2⟩
    (upperTranslationAt l) (pureMixed_upperTranslation_bar n c pure k l)]
  rw [upperTranslationAt_radical_conjugate]
  rfl

theorem normalizedBadLine_cyclic_mixed_primitive (n : ℕ) (positive : 0 < n)
    (f : HomogeneousPoly n) (solution : SymmetricSolution f)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (normalized : NormalizedBadLine f c) :
    ∃ a b : HomogeneousPoly n, ∃ correction : ℤ → HomogeneousPoly n,
      pderiv 0 a.val = 0 ∧ pderiv 0 b.val = 0 ∧
      (∀ k l, correction (k+l) = correction k+
        rationalCoefficientComponent n trivialCharacter (upperTranslationAt k) (correction l)) ∧
      ∀ k s t : ℤ,
      mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c (upperTranslationAt k)
          (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) +
        rationalCoefficientComponent n trivialCharacter (upperTranslationAt k) (s • a+(k*s+t) • b) -
        (s • a+t • b) =
      correction k-rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) (correction k) := by
  obtain ⟨a,b,p,ha,hb,generator⟩ := normalizedBadLine_upper_mixed_primitive n positive f solution c normalized
  obtain ⟨correction,relation,values⟩ := integerCocycle_lift
    ((rationalCoefficientComponent n trivialCharacter).comp upperTranslationHom)
    (radicalFunctionRepresentation n) (radicalBoundary n) (radicalBoundary_equivariant n)
    (cyclicMixedValue n c) (cyclicMixedValue_cocycle n c normalized.1)
    (fun x : ℤ × ℤ => x.1 • a+x.2 • b) p (by
      funext x
      simpa only [cyclicMixedValue,upperTranslationAt_one,radicalFunctionRepresentation,
        MonoidHom.coe_mk,OneHom.coe_mk,LinearMap.coe_mk,AddHom.coe_mk,Pi.sub_apply,Pi.add_apply,
        radicalBoundary,integralRadicalHom,shearPair,toAdd_ofAdd,one_mul] using generator x.1 x.2)
  exact ⟨a,b,correction,ha,hb,relation,fun k s t => congrFun (values k) (s,t)⟩

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
