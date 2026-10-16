module

public import TernaryPeriodPolynomials.ModularForm.ModularPeriod.Symmetry
public import TernaryPeriodPolynomials.PeriodPolynomial.ComplexPeriod.Space

@[expose] public section


noncomputable section
open MvPolynomial

namespace TernaryPoly.BinaryCuspPeriod

/-- The literal three-term defect of the actual odd Mellin period map. -/
def threeTermDefect (d : ℕ) : Forms d →ₗ[ℂ] MvPolynomial (Fin 2) ℂ :=
  oddPeriodLinearMap d -
    (bind₁ ![X 0-X 1, X 1]).toLinearMap.comp (oddPeriodLinearMap d) +
    (bind₁ ![X 0, X 0-X 1]).toLinearMap.comp (oddPeriodLinearMap d)

@[simp] theorem threeTermDefect_apply {d : ℕ} (f : Forms d) :
    threeTermDefect d f = oddPeriod f - bind₁ ![X 0-X 1, X 1] (oddPeriod f) +
      bind₁ ![X 0, X 0-X 1] (oddPeriod f) := rfl

/-- For the actual even-degree cusp period, only the literal three-term identity remains to
establish membership in the full period relations. -/
theorem relations_iff_threeTerm {d : ℕ} (hd : Even d) (f : Forms d) :
    BinaryComplexPeriod.Relations ℂ (oddPeriod f) ↔ threeTermDefect d f = 0 := by
  constructor
  · intro h
    exact h.2.2.2
  · intro h
    exact ⟨oddPeriod_swap hd f, oddPeriod_odd_first f, oddPeriod_odd_second hd f, h⟩

theorem mem_space_iff_threeTerm {d : ℕ} (hd : Even d) (f : Forms d) :
    oddPeriod f ∈ BinaryComplexPeriod.space ℂ d ↔ threeTermDefect d f = 0 := by
  constructor
  · intro h
    exact (relations_iff_threeTerm hd f).mp h.2
  · intro h
    exact ⟨oddPeriod_isHomogeneous f, (relations_iff_threeTerm hd f).mpr h⟩

/-- The explicitly defined kernel on which the actual period map already lands in the target.
No claim that this kernel is all cusp forms is included in this definition. -/
def threeTermKernel (d : ℕ) : Submodule ℂ (Forms d) := LinearMap.ker (threeTermDefect d)

/-- A genuine restricted linear map from actual cusp forms in the explicit three-term kernel. -/
def kernelPeriodMap (d : ℕ) (hd : Even d) :
    threeTermKernel d →ₗ[ℂ] BinaryComplexPeriod.space ℂ d where
  toFun f := ⟨oddPeriod f.val, (mem_space_iff_threeTerm hd f.val).mpr f.property⟩
  map_add' f g := Subtype.ext (oddPeriod_add f.val g.val)
  map_smul' c f := Subtype.ext (oddPeriod_smul f.val c)

/-- The full actual cusp-to-period map under exactly the three-term theorem. -/
def periodMapOfThreeTerm (d : ℕ) (hd : Even d)
    (hthree : ∀ f : Forms d, threeTermDefect d f = 0) :
    Forms d →ₗ[ℂ] BinaryComplexPeriod.space ℂ d where
  toFun f := ⟨oddPeriod f, (mem_space_iff_threeTerm hd f).mpr (hthree f)⟩
  map_add' f g := Subtype.ext (oddPeriod_add f g)
  map_smul' c f := Subtype.ext (oddPeriod_smul f c)

/-- The restricted target's extreme coordinate is exactly the normalized literal
XY^(d-1) coefficient of the actual polynomial. -/
theorem extreme_kernelPeriodMap (d : ℕ) (hd : Even d) (f : threeTermKernel d) :
    BinaryComplexPeriod.extreme ℂ d (kernelPeriodMap d hd f) =
      (oddPeriod f.val).coeff (exponent d 1) := rfl

/-- The same literal coordinate identity for the full map, with its three-term input explicit. -/
theorem extreme_periodMapOfThreeTerm (d : ℕ) (hd : Even d)
    (hthree : ∀ f : Forms d, threeTermDefect d f = 0) (f : Forms d) :
    BinaryComplexPeriod.extreme ℂ d (periodMapOfThreeTerm d hd hthree f) =
      (oddPeriod f).coeff (exponent d 1) := rfl

end TernaryPoly.BinaryCuspPeriod
