module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Locality.Cell.Support
public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellRep
public import TernaryPeriodPolynomials.SymmetricSpace.Bordified.Cohomology

@[expose] public section


/-!
# Lemma 3.3, G3: the cellular chain map into the symmetric space

The cell chains `cellAtSpace n C` of the symmetric space (the interior of the bordification) are
`Γ(6)`-equivariant (`smul_cellAtSpace`) and satisfy the boundary formula of the cellular complex
(`d_cellAtSpace`), so they define a chain map `cellChainMapS` of the cellular permutation complex into the
equivariant singular chains of the symmetric space, and `cellCoinvMapS W` with coefficients in `W` into the
coinvariant chains (`cellCoinvMapS_mk` : `[w ⊗ C] ↦ [w ⊗ cellAtSpace n C]`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.Lemma33.Locality

open CategoryTheory Limits Finsupp TernaryPoly TernaryPoly.SymmetricSpacePositive
  TernaryPoly.SingularCoverNaturality TernaryPoly.EquivariantSingularResolution
  SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision
  TernaryPoly.ContractibleSingularHomology TernaryPoly.FreeActionLinearization
  TernaryPoly.CoveringSingularOrbits TernaryPoly.SingularLocalHomology TernaryPoly.SingularLocalCoefficient
  TernaryPoly.IntegralGL3Congruence
  TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.Argument.Lemma33.Retract
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.LocalDegree
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry

theorem d_cellAtSpace (n : ℕ) (C : Cell) (hC : C.grade = n + 1) :
    ((underlyingChains SpaceTop).d (n + 1) n).hom (cellAtSpace (n + 1) C) =
      (incQ C).sum fun D a => a • cellAtSpace n D := by
  unfold cellAtSpace
  rw [realizeS_eq_via, d_realizeVia, coneData.phi_boundary n C hC, realizeVia_Phi]
  rfl

/-- The degree-`n` component of the cellular chain map into the symmetric space. -/
def cellChainFS (n : ℕ) : cellRep n ⟶ chainRep principalSix SpaceTop n :=
  permHomTo _ (linearCombination ℚ (fun C : Graded n => cellAtSpace n C.1)) (fun g C => by
    simp only [linearCombination_single, one_smul]
    exact (smul_cellAtSpace g n C.1).symm)

theorem cellChainFS_single (n : ℕ) (C : Graded n) :
    (cellChainFS n).hom (MonoidAlgebra.single C 1) = cellAtSpace n C.1 := by
  change linearCombination ℚ (fun C : Graded n => cellAtSpace n C.1)
    ((MonoidAlgebra.coeffLinearEquiv ℚ) (MonoidAlgebra.single C 1)) = _
  have h : (MonoidAlgebra.coeffLinearEquiv ℚ) (MonoidAlgebra.single C (1 : ℚ)) =
      (single C 1 : Graded n →₀ ℚ) := rfl
  rw [h, linearCombination_single, one_smul]

theorem lin_cellDS (j : ℕ) (w : Graded (j + 1) →₀ ℚ) :
    linearCombination ℚ (fun C : Graded j => cellAtSpace j C.1) (dLin j w) =
      ((underlyingChains SpaceTop).d (j + 1) j).hom
        (linearCombination ℚ (fun C : Graded (j + 1) => cellAtSpace (j + 1) C.1) w) := by
  have h : (linearCombination ℚ (fun C : Graded j => cellAtSpace j C.1)) ∘ₗ dLin j =
      ((underlyingChains SpaceTop).d (j + 1) j).hom ∘ₗ
        linearCombination ℚ (fun C : Graded (j + 1) => cellAtSpace (j + 1) C.1) := by
    apply Finsupp.lhom_ext
    intro C a
    have e : (single C a : Graded (j + 1) →₀ ℚ) = a • single C 1 := by simp
    rw [e]
    simp only [LinearMap.comp_apply, map_smul, dLin, linearCombination_single, one_smul]
    congr 1
    have h1 : linearCombination ℚ (fun D : Graded j => cellAtSpace j D.1) (dGr j C) =
        linearCombination ℚ (cellAtSpace j) (incl j (dGr j C)) := by
      rw [incl, Finsupp.lmapDomain_apply, linearCombination_mapDomain]
      rfl
    rw [h1, incl_dGr, d_cellAtSpace j C.1 C.2]
    rfl
  exact LinearMap.congr_fun h w

/-- **The cellular chain map into the equivariant singular chains of the symmetric space.** -/
def cellChainMapS : cellPermComplex ⟶ equivariantChains principalSix SpaceTop where
  f := cellChainFS
  comm' := by
    intro i j hij
    obtain rfl : j + 1 = i := hij
    have hd : cellPermComplex.d (j + 1) j = cellD j := ChainComplex.of_d _ _ _
    rw [hd]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    change ((underlyingChains SpaceTop).d (j + 1) j).hom
        (linearCombination ℚ (fun C : Graded (j + 1) => cellAtSpace (j + 1) C.1)
          (MonoidAlgebra.coeffLinearEquiv ℚ z)) =
      linearCombination ℚ (fun C : Graded j => cellAtSpace j C.1)
        ((MonoidAlgebra.coeffLinearEquiv ℚ) ((MonoidAlgebra.coeffLinearEquiv ℚ).symm
          (dLin j (MonoidAlgebra.coeffLinearEquiv ℚ z))))
    rw [LinearEquiv.apply_symm_apply]
    exact (lin_cellDS j _).symm

/-- The cellular chain map with coefficients in `W`, into the coinvariant chains of the symmetric space. -/
def cellCoinvMapS (W : Rep ℚ principalSix) :
    cellCoinv W ⟶ SingularLocalHomology.coinvariantChains principalSix SpaceTop W :=
  (((Rep.coinvariantsTensor ℚ principalSix).obj W).mapHomologicalComplex (ComplexShape.down ℕ)).map
    cellChainMapS

theorem cellCoinvMapS_mk (W : Rep ℚ principalSix) (n : ℕ) (w : W) (C : Graded n) :
    (cellCoinvMapS W).f n (Rep.coinvariantsTensorMk W (cellRep n) w (MonoidAlgebra.single C 1)) =
      Rep.coinvariantsTensorMk W (chainRep principalSix SpaceTop n) w (cellAtSpace n C.1) := by
  have h := SingularLocalHomology.tensorCoinvariant_map_mk W (cellRep n)
    (chainRep principalSix SpaceTop n) (cellChainFS n) w (MonoidAlgebra.single C 1)
  rw [cellChainFS_single] at h
  exact h

end TernaryPeriodPolynomials.Argument.Lemma33.Locality
