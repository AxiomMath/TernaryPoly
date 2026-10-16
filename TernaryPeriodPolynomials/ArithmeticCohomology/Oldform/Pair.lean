module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.Parity
public import TernaryPeriodPolynomials.ArithmeticCohomology.Oldform.Independence
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Vectors
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.Inputs
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.CohomologicalHolomorphic
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.ScalarHecke

@[expose] public section


/-!
# The oldform pair of a spherical inducing datum

For `D` with spherical cusp `σ = D.cusp`, the degree `n` is odd (`odd_of_sphericalCusp`), so the
level-one extraction gives a nonzero spherical vector `v` of rotation weight `-(n+3)`
(`cohomological_exists_spherical_holomorphic`).  Its Atkin–Lehner translate
`v' = cuspFiniteRationalSlash σ W v`, `W = [[0,-1],[3,0]]`, is fixed by the matrices of `GL₂(ℤ̂)`
upper triangular modulo three (`slashW_borel_fixed`), hence lies in the level-three
values, and has the same rotation weight.  So `v` and `v'` are two level-three weight vectors, and
they are linearly independent (`linearIndependent_atkinLehner`): the vectors of `f(τ)` and
`f(3τ)`.

* `exists_oldformPair`: two linearly independent vectors of
  `levelThreeWeightVectors D.cusp (sourceWeight n)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.LevelThreeSource
  (levelThreeWeightVectors sourceWeight levelThreeWeightVectors_mem_of_spherical)

namespace TernaryPeriodPolynomials.Oldform

open TernaryPeriodPolynomials.MultiplicityOne (atkinLehnerQ levelThreeValues
  cuspSphericalValues_le_levelThreeValues slashW_borel_fixed mem_borelThree)

variable {n : ℕ}

/-- **The oldform pair.**  A spherical inducing datum has two linearly independent level-three
vectors of the cohomological rotation weight `-(n+3)`: a spherical vector and its Atkin–Lehner
translate. -/
theorem exists_oldformPair (D : InducingData n) (hsph : SphericalCusp D.cusp) :
    ∃ v : Fin 2 → levelThreeWeightVectors D.cusp (sourceWeight n), LinearIndependent ℂ v := by
  have hodd := odd_of_sphericalCusp hsph D.cohomological
  obtain ⟨halfWeight, v, hweight, hv0, hsv, hrot, -, -⟩ :=
    cohomological_exists_spherical_holomorphic D.cusp hsph hodd D.cohomological
  have e : sourceWeight n = 2 * halfWeight := hweight.symm
  have hrot' : ∀ angle : Circle, D.cusp.π (atInfinity (binaryRotations angle)) v.val =
      (angle : ℂ) ^ (sourceWeight n) • v.val := by
    intro angle
    rw [e]
    exact hrot angle
  have hlevel : v.val ∈ levelThreeValues D.cusp :=
    cuspSphericalValues_le_levelThreeValues D.cusp hsv
  have hv : v ∈ levelThreeWeightVectors D.cusp (sourceWeight n) :=
    levelThreeWeightVectors_mem_of_spherical hsv hrot'
  have hw : cuspFiniteRationalSlash D.cusp atkinLehnerQ v ∈
      levelThreeWeightVectors D.cusp (sourceWeight n) :=
    ⟨fun k hk => slashW_borel_fixed D.cusp halfWeight v hlevel hrot k (mem_borelThree.mpr hk.1),
      cuspFiniteRationalSlash_rotation D.cusp atkinLehnerQ _ v hrot'⟩
  refine ⟨![⟨v, hv⟩, ⟨cuspFiniteRationalSlash D.cusp atkinLehnerQ v, hw⟩],
    LinearIndependent.of_comp (levelThreeWeightVectors D.cusp (sourceWeight n)).subtype ?_⟩
  have hcomp : (levelThreeWeightVectors D.cusp (sourceWeight n)).subtype ∘
      ![⟨v, hv⟩, ⟨cuspFiniteRationalSlash D.cusp atkinLehnerQ v, hw⟩] =
      ![v, cuspFiniteRationalSlash D.cusp atkinLehnerQ v] := by
    funext i
    fin_cases i <;> rfl
  rw [hcomp]
  exact linearIndependent_atkinLehner D.cusp v hv0 hsv

end TernaryPeriodPolynomials.Oldform
