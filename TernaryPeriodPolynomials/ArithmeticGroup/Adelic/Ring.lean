module

public import TernaryPeriodPolynomials.ArithmeticGroup.Adelic.Finite
public import Mathlib.Basic.Real.Basic

@[expose] public section




/-! The genuine rational adele ring and its actual rational and local general linear maps. -/
noncomputable section
namespace GeneralEisenstein.Adelic
open Matrix

/-- The rational adeles with the actual archimedean and finite factors. -/
abbrev Adeles := ℝ × FiniteAdeles

/-- The actual adelic general linear group in dimension three. -/
abbrev AdelicGL := GeneralLinearGroup (Fin 3) Adeles

/-- The actual diagonal rational embedding into the full adele ring. -/
def rationalAdele : ℚ →+* Adeles :=
  (algebraMap ℚ ℝ).prod (algebraMap ℚ FiniteAdeles)

/-- The actual real coordinate of a rational adele. -/
@[simp] theorem rationalAdele_real (q : ℚ) : (rationalAdele q).1 = (q : ℝ) := rfl

/-- The actual finite coordinate of a rational adele. -/
@[simp] theorem rationalAdele_finite (q : ℚ) :
    (rationalAdele q).2 = algebraMap ℚ FiniteAdeles q := rfl

/-- The genuine diagonal rational embedding is injective. -/
theorem rationalAdele_injective : Function.Injective rationalAdele := by
  intro q r h
  exact Rat.cast_injective (congrArg Prod.fst h : (q : ℝ) = (r : ℝ))

/-- The actual diagonal rational matrix embedding into the adelic group. -/
def rationalGroup : RationalGL →* AdelicGL := GeneralLinearGroup.map rationalAdele

/-- The actual archimedean projection of the adelic matrix group. -/
def realGroup : AdelicGL →* GeneralLinearGroup (Fin 3) ℝ :=
  GeneralLinearGroup.map (RingHom.fst ℝ FiniteAdeles)

/-- The actual finite projection of the adelic matrix group. -/
def finiteGroup : AdelicGL →* FiniteGL := GeneralLinearGroup.map (RingHom.snd ℝ FiniteAdeles)

/-- The actual finite projection commutes with the actual rational diagonal embedding. -/
theorem finiteGroup_rational (g : RationalGL) : finiteGroup (rationalGroup g) = rationalFinite g := rfl

/-- The actual archimedean projection commutes with the rational diagonal embedding. -/
theorem realGroup_rational (g : RationalGL) :
    realGroup (rationalGroup g) = GeneralLinearGroup.map (algebraMap ℚ ℝ) g := rfl

/-- The actual rational matrix embedding is injective. -/
theorem rationalGroup_injective : Function.Injective rationalGroup := by
  intro g h he
  apply GeneralLinearGroup.ext
  intro i j
  exact rationalAdele_injective (congrArg (fun a : AdelicGL => a.val i j) he)

end GeneralEisenstein.Adelic

end
