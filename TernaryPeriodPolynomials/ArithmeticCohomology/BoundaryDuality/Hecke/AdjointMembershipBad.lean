module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembership
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Hecke.AdjointMembershipFiber
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.L2Assembly

@[expose] public section


/-!
# The `U`-primitive of the line cocycle at the bad line `L₀`

At the bad line `L₀ = ⟨e₁⟩` (the standard bad line, the identity coset) the local cohomology is
described by Sol's inhomogeneous model: the stabilizer in the level is the split extension
`ℤ² ⋊ (ℤˣ × Γ₁'(3))` (`standardBadLineSemidirectEquiv`), with radical lattice
`I + x E₀₁ + y E₀₂`, which is the lattice `latL0` of the boundary trace. A local class has zero
radical restriction (it lies in `badLineLocalRadicalKernel`) exactly when the inhomogeneous
two-cocycle, pulled back to the radical along `inl`, is a coboundary. Unwinding the equivalences
between the ambient homogeneous model and the inhomogeneous model, this gives a one-cochain `f` on
the radical with `d f = c ∘ ι` in homogeneous coordinates, which is the input of
`HeckeAdjointMembershipEngine.classOf_pullback_eq_zero_of_primitive`.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic

namespace TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipBad

open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.FiberExact
open TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipEngine
open TernaryPeriodPolynomials.BoundaryDuality.L2Matrices
  (L₀ uL0 zuL0_val embedZ_apply)
open TernaryPeriodPolynomials.BoundaryDuality.L2Assembly (latL0 latL0_le)
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

variable {n : ℕ}

/-- The inclusion of the radical lattice into the stabilizer of the standard bad line. -/
def badLineRadicalIncl :
    Multiplicative (ℤ × ℤ) →* ↥(fixedPointLevel rationalLevel standardBadLine) :=
  standardBadLineSemidirectEquiv.toMonoidHom.comp SemidirectProduct.inl

/-- The inclusion is injective. -/
theorem badLineRadicalIncl_injective : Function.Injective badLineRadicalIncl :=
  fun _ _ h => SemidirectProduct.inl_injective (standardBadLineSemidirectEquiv.injective h)

/-- The value of the radical inclusion is the radical lattice element. -/
theorem badLineRadicalIncl_val (a : Multiplicative (ℤ × ℤ)) :
    (badLineRadicalIncl a).val = uL0 (Multiplicative.toAdd a).1 (Multiplicative.toAdd a).2 := by
  have h : (standardBadLineSemidirectEquiv (SemidirectProduct.inl a)).val =
      integralRational (lineUnipotent (Multiplicative.toAdd a).1 (Multiplicative.toAdd a).2) := by
    rw [standardBadLineSemidirectEquiv_inl]
    rfl
  change (standardBadLineSemidirectEquiv (SemidirectProduct.inl a)).val = _
  rw [h]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uL0, embedZ_apply, zuL0_val, integralRational, lineUnipotent, upperUnipotent,
      Matrix.GeneralLinearGroup.map_apply]

/-- Every element of the lattice of `L₀` is a value of the radical inclusion. -/
theorem latL0_mem_rad : ∀ u ∈ latL0.sub, ∃ a : Multiplicative (ℤ × ℤ),
    (badLineRadicalIncl a).val = (MonoidHom.id RationalGL3) u := by
  rintro _ ⟨p, rfl⟩
  exact ⟨p, badLineRadicalIncl_val p⟩

/-- **A primitive on the radical from a class in the radical kernel.** If the local class of a line
cocycle at the standard bad line has vanishing radical restriction, there is a one-cochain `f` on
the radical lattice with `d f = c ∘ ι`. -/
theorem exists_primitive_of_radicalKernel (z : MaximalCycles n trivialCharacter .line)
    (h : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      standardBadLine
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z) ∈
        LevelThree.BadLineLocal.badLineLocalRadicalKernel n) :
    ∃ f : Multiplicative (ℤ × ℤ) → HomogeneousPoly n,
      ∀ a b : Multiplicative (ℤ × ℤ),
        rationalCoefficientComponent n trivialCharacter (badLineRadicalIncl a).val (f b) -
            f (a * b) + f a =
          (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
            standardBadLine z).val.val
            ![1, (badLineRadicalIncl a).val, (badLineRadicalIncl a).val * (badLineRadicalIncl b).val] := by
  have hk := LinearMap.mem_ker.mp (Submodule.mem_comap.mp h)
  have hk' : (inhomogeneousBoundaries
      ((standardBadLineRepresentation n).comp SemidirectProduct.inl)).mkQ
      (inhomogeneousPullbackCycles SemidirectProduct.inl (standardBadLineRepresentation n)
        (fullInhomogeneousCycleEquiv (standardBadLineRepresentation n)
          (fullCycleEquiv standardBadLineSemidirectEquiv
            ((rationalCoefficientComponent n trivialCharacter).comp
              (fixedPointLevel rationalLevel standardBadLine).subtype)
            (ambientRestrictionCycles (fixedPointLevel rationalLevel standardBadLine)
              (rationalCoefficientComponent n trivialCharacter)
              (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
                standardBadLine z))))) = 0 := hk
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hk'
  obtain ⟨f, hf⟩ := LinearMap.mem_range.mp hk'
  refine ⟨f, fun a b => ?_⟩
  have hab := congrFun (congrFun (congrArg Subtype.val hf) a) b
  have key : (fun i : Fin 3 => (standardBadLineSemidirectEquiv
      (![1, SemidirectProduct.inl a, SemidirectProduct.inl a * SemidirectProduct.inl b] i)).val) =
      ![1, (badLineRadicalIncl a).val, (badLineRadicalIncl a).val * (badLineRadicalIncl b).val] := by
    funext i
    fin_cases i
    · simp
    · rfl
    · simp [badLineRadicalIncl]
  change rationalCoefficientComponent n trivialCharacter (badLineRadicalIncl a).val (f b) -
      f (a * b) + f a =
    (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
      standardBadLine z).val.val
      (fun i : Fin 3 => (standardBadLineSemidirectEquiv
        (![1, SemidirectProduct.inl a, SemidirectProduct.inl a * SemidirectProduct.inl b] i)).val)
    at hab
  rw [key] at hab
  exact hab

/-- **The line `U`-restriction at the bad line is exact for a class in the radical kernel.** -/
theorem classOf_lineRestriction_badLine_eq_zero (z : MaximalCycles n trivialCharacter .line)
    (Lf : Flags .line) (hLf : Lf = standardBadLine) (U : Subgroup RationalGL3)
    (hU : U ≤ levelStabilizer Lf)
    (hrad : ∀ u ∈ U, ∃ a : Multiplicative (ℤ × ℤ), (badLineRadicalIncl a).val = u)
    (h : fixedPointH2 rationalLevel (rationalCoefficientComponent n trivialCharacter)
      standardBadLine
      (classOf rationalLevel
        (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z) ∈
        LevelThree.BadLineLocal.badLineLocalRadicalKernel n) :
    classOf U (rationalCoefficientComponent n trivialCharacter)
      (lineRestriction z Lf U hU) = 0 := by
  subst hLf
  obtain ⟨f, hf⟩ := exists_primitive_of_radicalKernel z h
  exact classOf_pullback_eq_zero_of_primitive (rationalCoefficientComponent n trivialCharacter)
    (rationalCoefficientComponent n trivialCharacter) (MonoidHom.id RationalGL3) (fun _ => rfl)
    (levelStabilizer standardBadLine) U
    (fixedPointCycle rationalLevel (rationalCoefficientComponent n trivialCharacter)
      standardBadLine z)
    (lineRestriction z standardBadLine U hU) (fun _ => rfl) badLineRadicalIncl
    badLineRadicalIncl_injective f hf (fun u hu => hrad u hu)

/-- **The line `U`-restriction at `L₀` for a line summand class** (trivial character, `3 ≤ n`,
nonzero associate pair). -/
theorem classOf_lineRestriction_L₀_eq_zero (cusp : CuspidalRepresentation)
    (coh : Cohomological cusp n) (hecke : BoundaryHecke n trivialCharacter)
    (hhecke : ActualBoundaryHecke n trivialCharacter hecke) (hn : 3 ≤ n)
    (hne : associatePair (HeckeAdjointMembership.trivialData cusp coh) ≠ ⊥)
    (z : MaximalCycles n trivialCharacter .line)
    (hz : classOf rationalLevel
      (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z ∈
        boundarySummand (HeckeAdjointMembership.trivialData cusp coh) .line) :
    classOf latL0.sub (rationalCoefficientComponent n trivialCharacter)
      (lineRestriction z L₀ latL0.sub latL0_le) = 0 :=
  classOf_lineRestriction_badLine_eq_zero z L₀ rfl latL0.sub latL0_le
    (fun u hu => by
      obtain ⟨a, ha⟩ := latL0_mem_rad u hu
      exact ⟨a, ha⟩)
    (HeckeAdjointMembership.cuspRes_line_false_mem_radicalKernel cusp coh hecke hhecke hn hne hz)

end TernaryPeriodPolynomials.BoundaryDuality.HeckeAdjointMembershipBad
