module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BadLine.Innerness.RadicalPrimitive

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers

theorem representation_apply_injective {G V : Type*} [Group G] [AddCommGroup V]
    [Module ℂ V] (representation : Representation ℂ G V) (g : G) :
    Function.Injective (representation g) := by
  intro first second equal
  have canceled := congrArg (representation g⁻¹) equal
  simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
    map_one, Module.End.one_apply] using canceled

theorem integerPair_cocycle_ext {V : Type*} [AddCommGroup V] [Module ℂ V]
    (representation : Representation ℂ (Multiplicative (ℤ × ℤ)) V)
    (first second : ℤ × ℤ → V)
    (first_relation : ∀ x y, first (x+y) =
      first x + representation (Multiplicative.ofAdd x) (first y))
    (second_relation : ∀ x y, second (x+y) =
      second x + representation (Multiplicative.ofAdd x) (second y))
    (first_generator : first (1,0) = second (1,0))
    (second_generator : first (0,1) = second (0,1)) : first = second := by
  have first_zero : first 0 = 0 := by
    have relation := first_relation 0 0
    change first 0 = first 0 + representation 1 (first 0) at relation
    rw [map_one, Module.End.one_apply] at relation
    exact add_left_cancel (show first 0 + first 0 = first 0 + 0 by
      rw [← relation, add_zero])
  have second_zero : second 0 = 0 := by
    have relation := second_relation 0 0
    change second 0 = second 0 + representation 1 (second 0) at relation
    rw [map_one, Module.End.one_apply] at relation
    exact add_left_cancel (show second 0 + second 0 = second 0 + 0 by
      rw [← relation, add_zero])
  let equalizer : AddSubgroup (ℤ × ℤ) :=
    { carrier := {x | first x = second x}
      zero_mem' := first_zero.trans second_zero.symm
      add_mem' := by
        intro x y hx hy
        change first (x+y) = second (x+y)
        rw [first_relation, second_relation, hx, hy]
      neg_mem' := by
        intro x hx
        change first (-x) = second (-x)
        apply representation_apply_injective representation (Multiplicative.ofAdd x)
        have left := first_relation x (-x)
        have right := second_relation x (-x)
        rw [add_neg_cancel, first_zero, hx] at left
        rw [add_neg_cancel, second_zero] at right
        exact add_left_cancel (left.symm.trans right) }
  funext x
  have member := equalizer.add_mem (equalizer.zsmul_mem first_generator x.1)
    (equalizer.zsmul_mem second_generator x.2)
  change x.1 • ((1,0) : ℤ × ℤ) + x.2 • ((0,1) : ℤ × ℤ) ∈ equalizer at member
  have pair_eq : x.1 • ((1,0) : ℤ × ℤ) + x.2 • ((0,1) : ℤ × ℤ) = x := by
    ext <;> simp
  exact pair_eq ▸ member

def integralRadicalHom : Multiplicative (ℤ × ℤ) →* RationalGL3 where
  toFun p := Adelic.lineUnipotent (p.toAdd.1 : ℚ) (p.toAdd.2 : ℚ)
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' p q := by
    change Adelic.lineUnipotent ((p.toAdd.1 + q.toAdd.1 : ℤ) : ℚ)
      ((p.toAdd.2 + q.toAdd.2 : ℤ) : ℚ) = _
    rw [Int.cast_add, Int.cast_add, Adelic.lineUnipotent_add]

theorem mixedValue_integralRadical_cocycle (n : ℕ)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (pure : PureMixedBadLine c) (levi : rationalLevel)
    (normalizes : ∀ s t : ℤ, ∃ s' t' : ℤ,
      levi.val⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * levi.val =
        Adelic.lineUnipotent (s' : ℚ) (t' : ℚ)) (x y : ℤ × ℤ) :
    mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c levi.val
        (integralRadicalHom (Multiplicative.ofAdd (x+y))) =
      mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c levi.val
        (integralRadicalHom (Multiplicative.ofAdd x)) +
      rationalCoefficientComponent n trivialCharacter
        (integralRadicalHom (Multiplicative.ofAdd x))
        (mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c levi.val
          (integralRadicalHom (Multiplicative.ofAdd y))) := by
  change mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c levi.val
    (integralRadicalHom (Multiplicative.ofAdd x * Multiplicative.ofAdd y)) = _
  rw [map_mul]
  apply mixedValue_radical_cocycle rationalLevel
    (rationalCoefficientComponent n trivialCharacter) c levi
      ⟨integralRadicalHom (Multiplicative.ofAdd x), rationalLevel_lineUnipotent x.1 x.2⟩
  · exact pureMixed_radical_bar c pure x.1 x.2 y.1 y.2
  · obtain ⟨s,t,first_eq⟩ := normalizes x.1 x.2
    obtain ⟨s',t',second_eq⟩ := normalizes y.1 y.2
    change barValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c
      (levi.val⁻¹ * Adelic.lineUnipotent (x.1 : ℚ) (x.2 : ℚ) * levi.val)
      (levi.val⁻¹ * Adelic.lineUnipotent (y.1 : ℚ) (y.2 : ℚ) * levi.val) = 0
    rw [first_eq, second_eq]
    exact pureMixed_radical_bar c pure s t s' t'

theorem mixed_primitive_on_integralRadical_of_coordinate_zero (n : ℕ) (positive : 0 < n)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (pure : PureMixedBadLine c) (levi : rationalLevel)
    (normalizes : ∀ s t : ℤ, ∃ s' t' : ℤ,
      levi.val⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * levi.val =
        Adelic.lineUnipotent (s' : ℚ) (t' : ℚ))
    (coordinate_zero : mixedBernoulliCoordinate c levi.val = 0) :
    ∃ primitive : HomogeneousPoly n, ∀ s t : ℤ,
      mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c levi.val
        (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) =
      primitive - rationalCoefficientComponent n trivialCharacter
        (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) primitive := by
  obtain ⟨primitive, generators⟩ :=
    mixed_primitive_on_generators_of_coordinate_zero n positive c levi.val coordinate_zero
  let representation := (rationalCoefficientComponent n trivialCharacter).comp integralRadicalHom
  have equal := integerPair_cocycle_ext representation
    (fun x => mixedValue rationalLevel (rationalCoefficientComponent n trivialCharacter) c
      levi.val (integralRadicalHom (Multiplicative.ofAdd x)))
    (fun x => primitive - representation (Multiplicative.ofAdd x) primitive)
    (mixedValue_integralRadical_cocycle n c pure levi normalizes) (by
      intro x y
      change primitive - representation (Multiplicative.ofAdd x * Multiplicative.ofAdd y)
        primitive = _
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel)
    (by simpa [representation, integralRadicalHom] using
      generators 0)
    (by simpa [representation, integralRadicalHom] using
      generators 1)
  exact ⟨primitive, fun s t => congrFun equal (s,t)⟩

end TernaryPeriodPolynomials.PolynomialBadLineInnerness.Helpers
