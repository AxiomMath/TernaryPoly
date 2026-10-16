module

public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyPlaneComparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalPlaneNaturality
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalPlaneDetection
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyAlgebra
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyPlane
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologySubgroups
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantLevi
public import TernaryPeriodPolynomials.SymmetricSolution.LineCohomology.Naturality
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLineComparison
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyBB
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyBG
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Face.RadicalBinaryTransvections
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantPlaneInvariants
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantTwist
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLine
public import TernaryPeriodPolynomials.SymmetricSolution.LineCohomology.Levi
public import TernaryPeriodPolynomials.GroupCohomology.Relative.Edge.CohomologyPolynomials
public import TernaryPeriodPolynomials.GroupCohomology.Radical.CoinvariantAxis

@[expose] public section


/-!
# `tab:radical-cohomology` and `tab:edge-weights`: the `H¹` column, the Lie-algebra computation and the edge weights

Formalized by Claude Sonnet 5.5.

Throughout, `E = Sym^n((ℚ³)*)` with its left inverse-substitution action
(`PolynomialGLAction.integralAction n 0`), `N_P = ⟨U₁₃, U₂₃⟩ ≅ ℤ²` is the plane radical (`planeRep n`), `N_L = ⟨U₁₂, U₁₃⟩ ≅ ℤ²`
the line radical (`lineRep n`), `GL2 = GL₂(ℤ)`, and `BinaryH d` the binary forms of degree `d`.

* **`H¹` column of `tab:radical-cohomology`** ("These calculations give its first column"):
  `plane_radical_H1` identifies `H¹(N_P, E)` with `Sym^{n+1}(x,y)*` (a linear isomorphism onto `BinaryH (n+1)`, equal on cocycles to
  the degree-raised contraction `(a, b) ↦ x·a|_{z=0} + y·b|_{z=0}` of the two generator values) under which the Levi element
  `A ∈ GL₂(ℤ)` acts by the inverse substitution `A⁻¹` and no determinant twist; `line_radical_H1` identifies `H¹(N_L, E)` with
  `η⁻¹ det(D) Sym^{n+1}(y,z)*` for the Levi element `diag(η, D)`, `η = ±1`, `D ∈ GL₂(ℤ)`.  Both are the full Levi (not only
  the congruence subgroup `Γ₂`).
* **Lie-algebra computation of `H¹(N_R, E)`**: for the root operators `z∂_x, z∂_y` (`plane_lie_cocycle_equation`,
  `plane_lie_closed_iff_gradient`, `plane_lie_exact_iff`, `planeLieEquiv`): the cocycle equation is `a_y = b_x`; closed pairs
  are the gradients of homogeneous potentials of degree `n + 1`; exact pairs are the gradients of the potentials divisible by
  `z`; the quotient is `Sym^{n+1}(x,y)` by restriction of the potential to `z = 0`.  For the dual root operators
  (`x∂_z, y∂_z` up to the renaming `x ↔ z`, i.e. the line radical `y∂_x, z∂_x`; `line_lie_*`, `lineLieEquiv`): the contraction
  `(α, β) ↦ zα - yβ` is independent of `x` on closed pairs, kills exactly the exact pairs and is onto the binary forms of degree
  `n + 1` (Euler section).  The comparison of Lie and group cohomology for these abelian radicals is the explicit Todd
  isomorphism of the library (`plane_group_lie_comparison`, `line_group_lie_comparison`): `H¹` of the integral lattice `ℤ²`
  with coefficients `E` is the quotient `closed derivative pairs / exact derivative pairs`.  The Levi equivariance of the
  identifications is that of `plane_radical_H1`, `line_radical_H1`.  What is cited, not formalized: Kasuya's comparison theorem for
  arbitrary nilmanifolds; the library's comparison is the abelian case needed here.
* **`tab:edge-weights`**: `bb_first_weight`, `bb_second_weight`, `bg_first_weight`, `bg_second_weight` state
  the weights of the four one-dimensional spaces that form the two subquotients (`Statements.EdgeSubquotients`) of the edge cohomology
  `0 → H¹(ℤ, E^N) → H¹(N_edge, E) → H¹(N, E)^ℤ → 0` of the paper (`D₀ = {diag(η₁, η₂, 1)}`, `weight a₁ a₂` the
  character `η₁^{a₁} η₂^{a₂}`): the invariants `E^{N_P} = ℚz^n` and `E^{N_L} = ℚ[y,z]_n`, the coinvariants of the remaining root
  (`z^n` represents them), the line of the invariants of the remaining root in `H¹(N, E)` (`y^{n+1}`), and the `D₀`-eigenvalue
  on each, with the root-conjugation factors.  `edge_weights_nontrivial` is the parity statement of the caption.

**The edge sequence.**  The exactness of `0 → H¹(ℤ, E^N) → H¹(N_edge, E) → H¹(N, E)^ℤ → 0` (the low-degree sequence for the semidirect
product `N ⋊ ℤ`, with the surjectivity onto the invariants) and the identification of the four weighted spaces above as the two subquotients
of `H¹(N_edge, E)`, for both edges, are proved in `Statements.EdgeSubquotients` (`bb_edge_subquotients`, `bg_edge_subquotients`), which uses the
Levi-equivariant isomorphisms and the invariant lines of this file.  The library also proves the vanishing `H¹(H_BB, E) = H¹(H_BG, E) = 0` for even
`n` directly, by elimination of root values (`Statements.AlternatingEven.edge_stabilizer_H1_vanishing`).
-/

open TernaryPoly

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables

open CategoryTheory MvPolynomial TernaryPoly.RadicalCoinvariantAlgebra TernaryPoly.RadicalFirstCohomology
open TernaryPoly.OrdinaryFaceRadical TernaryPoly.RadicalFirstCohomologyLattice

/-- Closed pairs are gradients. -/
theorem plane_lie_closed_iff_gradient (n : ℕ) (a b : H n) :
    planeDerivativeCurl n ![a, b] = 0 ↔
      ∃ F : Poly, F.IsHomogeneous (n + 1) ∧ pderiv 0 F = (a : Poly) ∧ pderiv 1 F = (b : Poly) := by
  constructor
  · intro h
    have h' := congrArg (fun v : H n => (v : Poly)) h
    simp only [planeDerivativeCurl_coe] at h'
    exact RadicalFirstCohomologyAlgebra.plane_closed_potential a.property b.property
      (by simpa using h')
  · rintro ⟨F, hF, ha, hb⟩
    apply Subtype.ext
    rw [planeDerivativeCurl_coe]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ha, ← hb, MultivariateIntegral.pderiv_commute 0 1, Submodule.coe_zero]
    ring



/-- Exact pairs are gradients of potentials divisible by `z`. -/
theorem plane_lie_exact_iff (n : ℕ) (F : Poly) (hF : F.IsHomogeneous (n + 1)) :
    (∃ g : H n, (-X 2) * pderiv 0 (g : Poly) = pderiv 0 F ∧
        (-X 2) * pderiv 1 (g : Poly) = pderiv 1 F) ↔ ∃ q : Poly, F = X 2 * q := by
  rw [← erase_eq_zero_iff]
  constructor
  · rintro ⟨g, h0, h1⟩
    set G : Poly := F + X 2 * (g : Poly) with hG
    have hG0 : pderiv 0 G = 0 := by
      rw [hG, map_add, pderiv_mul, pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0)]
      linear_combination (-1 : Poly) * h0
    have hG1 : pderiv 1 G = 0 := by
      rw [hG, map_add, pderiv_mul, pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 1)]
      linear_combination (-1 : Poly) * h1
    have hGh : G.IsHomogeneous (n + 1) := by
      have h := (isHomogeneous_X ℚ 2).mul g.property
      rw [Nat.add_comm] at h
      exact hF.add h
    have hE := plane_erased_euler G hGh
    rw [← erase_pderiv_of_ne 2 0 (by decide), ← erase_pderiv_of_ne 2 1 (by decide),
      hG0, hG1] at hE
    simp only [map_zero, mul_zero, add_zero] at hE
    have hn : C ((n + 1 : ℕ) : ℚ) ≠ (0 : Poly) := C_ne_zero.mpr (by positivity)
    have hEG : erase 2 G = 0 := (mul_eq_zero.mp hE.symm).resolve_left hn
    have hF2 : erase 2 F = erase 2 G := by
      rw [hG, map_add, (erase_eq_zero_iff 2 (X 2 * (g : Poly))).mpr ⟨g, rfl⟩, add_zero]
    rw [hF2, hEG]
  · intro he
    obtain ⟨g, hg, h0, h1⟩ := RadicalFirstCohomologyAlgebra.plane_potential_exact hF he
    exact ⟨⟨g, hg⟩, h0, h1⟩

/-- The degree-raised contraction `(a, b) ↦ x·a|_{z=0} + y·b|_{z=0}` of a pair of coefficients: `(n+1)` times the
restriction to `z = 0` of a potential. -/
def pairContract (n : ℕ) : (Fin 2 → H n) →ₗ[ℚ] BinaryH (n + 1) where
  toFun v := ⟨X 0 * planeEvalAlg (v 0 : Poly) + X 1 * planeEvalAlg (v 1 : Poly), by
    change (X 0 * planeEvalAlg (v 0 : Poly) + X 1 * planeEvalAlg (v 1 : Poly)).IsHomogeneous (n + 1)
    simpa only [Nat.add_comm, planeEval_coe] using
      ((isHomogeneous_X ℚ 0).mul (planeEval n (v 0)).property).add
        ((isHomogeneous_X ℚ 1).mul (planeEval n (v 1)).property)⟩
  map_add' v w := by
    apply Subtype.ext
    change X 0 * planeEvalAlg ((v 0 : Poly) + (w 0 : Poly)) + X 1 * planeEvalAlg ((v 1 : Poly) + (w 1 : Poly)) =
      (X 0 * planeEvalAlg (v 0 : Poly) + X 1 * planeEvalAlg (v 1 : Poly)) +
        (X 0 * planeEvalAlg (w 0 : Poly) + X 1 * planeEvalAlg (w 1 : Poly))
    simp only [map_add]
    ring
  map_smul' r v := by
    apply Subtype.ext
    change X 0 * planeEvalAlg (r • (v 0 : Poly)) + X 1 * planeEvalAlg (r • (v 1 : Poly)) =
      r • (X 0 * planeEvalAlg (v 0 : Poly) + X 1 * planeEvalAlg (v 1 : Poly))
    simp [planeEvalAlg, Algebra.smul_def]
    ring

theorem pairContract_apply (n : ℕ) (v : Fin 2 → H n) :
    (pairContract n v : MvPolynomial (Fin 2) ℚ) =
      X 0 * planeEvalAlg (v 0 : Poly) + X 1 * planeEvalAlg (v 1 : Poly) := rfl

theorem planeEvalAlg_rename (q : MvPolynomial (Fin 2) ℚ) :
    planeEvalAlg (rename (![0, 1] : Fin 2 → Fin 3) q) = q := by
  have h : planeEvalAlg.comp (rename (![0, 1] : Fin 2 → Fin 3)) = AlgHom.id ℚ _ := by
    ext k; fin_cases k <;> simp [planeEvalAlg]
  exact DFunLike.congr_fun h q

/-- Every binary form of degree `n + 1` is the contraction of a closed pair (a gradient). -/
theorem pairContract_surjective (n : ℕ) (J : BinaryH (n + 1)) :
    ∃ v : Fin 2 → H n, planeDerivativeCurl n v = 0 ∧ pairContract n v = J := by
  set F : Poly := rename (![0, 1] : Fin 2 → Fin 3) (J : MvPolynomial (Fin 2) ℚ) with hFdef
  have hF : F.IsHomogeneous (n + 1) := J.property.rename_isHomogeneous
  let a : H n := ⟨pderiv 0 F, MultivariateIntegral.pderiv_homogeneous 0 hF⟩
  let b : H n := ⟨pderiv 1 F, MultivariateIntegral.pderiv_homogeneous 1 hF⟩
  have hclosed : planeDerivativeCurl n ![a, b] = 0 :=
    (plane_lie_closed_iff_gradient n a b).mpr ⟨F, hF, rfl, rfl⟩
  have hc : pairContract n ![a, b] = ((n + 1 : ℚ)) • J := by
    apply Subtype.ext
    rw [pairContract_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, a, b, hFdef]
    have h0 : pderiv (0 : Fin 3) (rename (![0, 1] : Fin 2 → Fin 3) (J : MvPolynomial (Fin 2) ℚ)) =
        rename (![0, 1] : Fin 2 → Fin 3) (pderiv (0 : Fin 2) (J : MvPolynomial (Fin 2) ℚ)) :=
      pderiv_rename (f := (![0, 1] : Fin 2 → Fin 3)) (by decide) 0 _
    have h1 : pderiv (1 : Fin 3) (rename (![0, 1] : Fin 2 → Fin 3) (J : MvPolynomial (Fin 2) ℚ)) =
        rename (![0, 1] : Fin 2 → Fin 3) (pderiv (1 : Fin 2) (J : MvPolynomial (Fin 2) ℚ)) :=
      pderiv_rename (f := (![0, 1] : Fin 2 → Fin 3)) (by decide) 1 _
    rw [h0, h1, planeEvalAlg_rename, planeEvalAlg_rename]
    have hE := J.property.sum_X_mul_pderiv
    rw [Fin.sum_univ_two] at hE
    rw [hE]
    change _ = (n + 1 : ℚ) • (J : MvPolynomial (Fin 2) ℚ)
    rw [← Nat.cast_smul_eq_nsmul ℚ]
    simp
  refine ⟨((n + 1 : ℚ)⁻¹) • ![a, b], ?_, ?_⟩
  · rw [map_smul, hclosed, smul_zero]
  · rw [map_smul, hc, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]

/-- A closed pair with zero contraction is exact. -/
theorem pairContract_ker (n : ℕ) (v : Fin 2 → H n) (hv : planeDerivativeCurl n v = 0)
    (h0 : pairContract n v = 0) : ∃ w : H n, planeDerivativePair n w = v := by
  have hv' : v = ![v 0, v 1] := by
    funext j; fin_cases j <;> rfl
  rw [hv'] at hv
  obtain ⟨F, hF, ha, hb⟩ := (plane_lie_closed_iff_gradient n (v 0) (v 1)).mp hv
  have hq : X 0 * erase 2 (v 0 : Poly) + X 1 * erase 2 (v 1 : Poly) = 0 := by
    have h := congrArg (fun p : BinaryH (n + 1) => rename (![0, 1] : Fin 2 → Fin 3)
      (p : MvPolynomial (Fin 2) ℚ)) h0
    simp only [pairContract_apply, map_add, map_mul, rename_X, plane_rename_eval] at h
    simpa using h
  have hclosed : pderiv 0 (erase 2 (v 1 : Poly)) = pderiv 1 (erase 2 (v 0 : Poly)) := by
    rw [← erase_pderiv_of_ne 2 0 (by decide), ← erase_pderiv_of_ne 2 1 (by decide), ← ha, ← hb,
      MultivariateIntegral.pderiv_commute 0 1]
  obtain ⟨ha0, hb0⟩ := plane_erased_contract_kernel (v 0 : Poly) (v 1 : Poly) (v 0).property
    (v 1).property hclosed hq
  have hE := plane_erased_euler F hF
  rw [← erase_pderiv_of_ne 2 0 (by decide), ← erase_pderiv_of_ne 2 1 (by decide), ha, hb, ha0, hb0]
    at hE
  simp only [mul_zero, add_zero] at hE
  have hn : C ((n + 1 : ℕ) : ℚ) ≠ (0 : Poly) := C_ne_zero.mpr (by positivity)
  have hF0 : erase 2 F = 0 := (mul_eq_zero.mp hE.symm).resolve_left hn
  obtain ⟨g, hg, h1, h2⟩ := RadicalFirstCohomologyAlgebra.plane_potential_exact hF hF0
  refine ⟨⟨g, hg⟩, ?_⟩
  funext j
  fin_cases j
  · apply Subtype.ext
    change ((planeDerivativePair n ⟨g, hg⟩ 0 : H n) : Poly) = (v 0 : Poly)
    rw [planeDerivativePair_zero, planeFirstDerivative_coe]
    change (-X 2) * pderiv 0 g = (v 0 : Poly)
    rw [h1, ha]
  · apply Subtype.ext
    change ((planeDerivativePair n ⟨g, hg⟩ 1 : H n) : Poly) = (v 1 : Poly)
    rw [planeDerivativePair_one, planeSecondDerivative_coe]
    change (-X 2) * pderiv 1 g = (v 1 : Poly)
    rw [h2, hb]

/-- The contraction kills every exact pair. -/
theorem pairContract_pair (n : ℕ) (w : H n) : pairContract n (planeDerivativePair n w) = 0 := by
  apply Subtype.ext
  rw [pairContract_apply, planeDerivativePair_zero, planeDerivativePair_one, planeFirstDerivative_coe,
    planeSecondDerivative_coe]
  simp [planeEvalAlg]

/-- The contraction descends to the Lie quotient `closed pairs / exact pairs`. -/
def planeLieMap (n : ℕ) : planeDerivativeQuotient n →ₗ[ℚ] BinaryH (n + 1) :=
  Submodule.liftQ (LinearMap.range (planeDerivativeComplex n).moduleCatToCycles)
    ((pairContract n).comp (LinearMap.ker (planeDerivativeCurl n)).subtype) (by
      rintro _ ⟨w, rfl⟩
      exact pairContract_pair n w)

theorem planeLieMap_mk (n : ℕ) (v : planeDerivativeClosedPairs n) :
    planeLieMap n (Submodule.Quotient.mk v) = pairContract n v.val := rfl

/-- **The Lie-algebra computation of `H¹(N_P, E)` (root operators `z∂_x, z∂_y`):** closed pairs modulo
exact pairs are the binary forms of degree `n + 1` by restriction of the potential to `z = 0`. -/
def planeLieEquiv (n : ℕ) : planeDerivativeQuotient n ≃ₗ[ℚ] BinaryH (n + 1) :=
  LinearEquiv.ofBijective (planeLieMap n) ⟨by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : pairContract n v.val = 0 := hx
    obtain ⟨w, hw⟩ := pairContract_ker n v.val v.property hx'
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, Subtype.ext hw⟩, by
    intro J
    obtain ⟨v, hv, hJ⟩ := pairContract_surjective n J
    exact ⟨Submodule.Quotient.mk ⟨v, hv⟩, hJ⟩⟩

open groupCohomology RelativeStabilizerParameters TernaryPoly.RadicalTopCohomology TernaryPoly.LatticeTopCohomology

theorem planeH1π_surjective (n : ℕ) : Function.Surjective (H1π (planeRep n)) :=
  (ModuleCat.epi_iff_surjective _).mp inferInstance

theorem planeH1π_ker (n : ℕ) :
    LinearMap.ker (H1π (planeRep n)).hom = LinearMap.ker (planeCocycleContract n) := by
  ext c
  exact (planeCocycleContract_eq_zero_iff n c).symm

/-- The contraction on group cocycles descends to the first cohomology. -/
def planeH1Contract (n : ℕ) : groupCohomology (planeRep n) 1 →ₗ[ℚ] BinaryH (n + 1) :=
  ((LinearMap.ker (H1π (planeRep n)).hom).liftQ (planeCocycleContract n) (planeH1π_ker n).le).comp
    ((H1π (planeRep n)).hom.quotKerEquivOfSurjective (planeH1π_surjective n)).symm.toLinearMap

theorem planeH1Contract_H1π (n : ℕ) (c : cocycles₁ (planeRep n)) :
    planeH1Contract n (H1π (planeRep n) c) = planeCocycleContract n c := by
  simp [planeH1Contract]

theorem planeH1Contract_injective (n : ℕ) : Function.Injective (planeH1Contract n) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm ?_ bot_le
  intro x hx
  change x = 0
  change planeH1Contract n x = 0 at hx
  revert hx
  refine H1_induction_on x ?_
  intro c hc
  rw [planeH1Contract_H1π] at hc
  exact (planeCocycleContract_eq_zero_iff n c).mp hc

theorem planeH1Contract_surjective (n : ℕ) : Function.Surjective (planeH1Contract n) := by
  let _ : Module.Finite ℚ (BinaryH (n + 1)) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 2) ℚ (n + 1))
  let e0 : groupCohomology (planeRep n) 1 ≃ₗ[ℚ] BinaryH (n + 1) :=
    (planeH1DerivativeQuotientIso n).toLinearEquiv.trans (planeLieEquiv n)
  have _ : FiniteDimensional ℚ (groupCohomology (planeRep n) 1) :=
    LinearEquiv.finiteDimensional e0.symm
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank e0.finrank_eq).mp
    (planeH1Contract_injective n)

theorem planeH1Contract_Levi (n : ℕ) (A : GL2) (x : groupCohomology (planeRep n) 1) :
    (planeH1Contract n (planeH1Action n A x) : MvPolynomial (Fin 2) ℚ) =
      binaryMatrixSubst (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) A⁻¹).val
        (planeH1Contract n x : MvPolynomial (Fin 2) ℚ) := by
  refine H1_induction_on x ?_
  intro c
  change (planeH1Contract n (groupCohomology.map (matrixLattice A⁻¹).toMonoidHom (planeCoefficientHom n A) 1
      (H1π (planeRep n) c)) : MvPolynomial (Fin 2) ℚ) = _
  rw [H1π_comp_map_apply, planeH1Contract_H1π, planeH1Contract_H1π]
  exact planeCocycleContract_Levi n A c

/-- **`H¹` column of `tab:radical-cohomology`, plane radical.**
`H¹(N_P,E) ≅ Sym^{n+1}(x,y)*`: an identification of the first cohomology of the plane radical
`N_P = ⟨U₁₃,U₂₃⟩ ≅ ℤ²` with binary forms of degree `n + 1` (restriction of the potential to `z = 0`; on cocycles it is the
degree-raised contraction `(a, b) ↦ x·a|_{z=0} + y·b|_{z=0}`), under which the Levi element `A ∈ GL₂(ℤ)` acts by the inverse
substitution `A⁻¹`, with no determinant twist. -/
theorem plane_radical_H1 (n : ℕ) :
    ∃ e : groupCohomology (planeRep n) 1 ≃ₗ[ℚ] BinaryH (n + 1),
      (∀ c : cocycles₁ (planeRep n), e (H1π (planeRep n) c) = planeCocycleContract n c) ∧
      ∀ (A : GL2) (v : groupCohomology (planeRep n) 1),
        (e (planeH1Action n A v) : MvPolynomial (Fin 2) ℚ) =
          binaryMatrixSubst (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) A⁻¹).val
            (e v : MvPolynomial (Fin 2) ℚ) :=
  ⟨LinearEquiv.ofBijective (planeH1Contract n) ⟨planeH1Contract_injective n, planeH1Contract_surjective n⟩,
    planeH1Contract_H1π n, planeH1Contract_Levi n⟩

open TernaryPoly.SymmetricLineCohomology

/-- The Levi action of `diag(t, L)` on the lattice coefficient representation of the line radical, for the
**untwisted** coefficients `E = Sym^n((ℚ³)*)` (determinant exponent `0`): the coefficient map is the plain inverse
substitution by the Levi element. -/
def leviCoefficientHom0 (n : ℕ) (t : ℤˣ) (L : GL2) :
    Rep.res (leviLatticeChange t L) (lineRep n) ⟶ lineRep n :=
  Rep.ofHom ⟨PolynomialGLAction.integralAction n 0 (lineElement t 0 L), by
    intro g
    change PolynomialGLAction.integralAction n 0 (lineElement t 0 L) *
      (lineRep n).ρ (leviLatticeChange t L g) =
      (lineRep n).ρ g * PolynomialGLAction.integralAction n 0 (lineElement t 0 L)
    rw [← lineHom_action_twist n 0, ← lineHom_action_twist n 0,
      ← map_mul, ← map_mul, leviLatticeChange_commute]⟩

/-- The conjugation action of the Levi element `diag(t, L)` on `H¹(N_L, E)`, `E = Sym^n((ℚ³)*)`. -/
def lineH1LeviAction0 (n : ℕ) (t : ℤˣ) (L : GL2) :
    groupCohomology (lineRep n) 1 ⟶ groupCohomology (lineRep n) 1 :=
  groupCohomology.map (leviLatticeChange t L) (leviCoefficientHom0 n t L) 1

theorem integralAction_zero_eq (n : ℕ) (t : ℤˣ) (L : GL2) (v : H n) :
    (PolynomialGLAction.integralAction n 0 (lineElement t 0 L) v : Poly) =
      ((t.val : ℚ) * (L.val.det : ℚ)) •
        (PolynomialGLAction.integralAction n (-1) (lineElement t 0 L) v : Poly) := by
  have hne : (t.val : ℚ) * (L.val.det : ℚ) ≠ 0 := by
    have h1 : (t.val : ℚ) ≠ 0 := by
      rcases Int.units_eq_one_or t with rfl | rfl <;> norm_num
    have h2 : (L.val.det : ℚ) ≠ 0 := by
      have := (Matrix.GeneralLinearGroup.det L).ne_zero
      exact_mod_cast this
    exact mul_ne_zero h1 h2
  rw [PolynomialGLAction.integralAction_coe, PolynomialGLAction.integralAction_coe,
    PolynomialGLAction.action_apply, PolynomialGLAction.action_apply, lineLevi_character]
  rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  simp [PolynomialGLAction.determinantCharacter]

theorem lineH1LeviAction0_eq (n : ℕ) (t : ℤˣ) (L : GL2) (x : groupCohomology (lineRep n) 1) :
    lineH1LeviAction0 n t L x =
      ((t.val : ℚ) * (L.val.det : ℚ)) • latticeH1LeviAction n t L x := by
  refine H1_induction_on x ?_
  intro c
  have hc : mapCocycles₁ (leviLatticeChange t L) (leviCoefficientHom0 n t L) c =
      ((t.val : ℚ) * (L.val.det : ℚ)) •
        mapCocycles₁ (leviLatticeChange t L) (leviCoefficientHom n t L) c := by
    apply cocycles₁_ext
    intro g
    exact Subtype.ext (integralAction_zero_eq n t L _)
  change groupCohomology.map (leviLatticeChange t L) (leviCoefficientHom0 n t L) 1 (H1π (lineRep n) c) =
    ((t.val : ℚ) * (L.val.det : ℚ)) • groupCohomology.map (leviLatticeChange t L) (leviCoefficientHom n t L) 1
      (H1π (lineRep n) c)
  rw [H1π_comp_map_apply, H1π_comp_map_apply, hc]
  exact map_smul (H1π (lineRep n)).hom _ _

/-- **`H¹` column of `tab:radical-cohomology`, line radical.**
`H¹(N_L,E) ≅ η^{-1} det(D) Sym^{n+1}(y,z)*`: an identification of the first cohomology of the line radical
`N_L = ⟨U₁₂,U₁₃⟩ ≅ ℤ²` with binary forms of degree `n + 1` in `y, z` (the contraction `(α, β) ↦ zα - yβ` of the
Todd-converted cocycle), under which the Levi element `diag(η, D)`, `η = ±1`, `D ∈ GL₂(ℤ)`, acts by the dual binary
action `J ↦ J∘D⁻¹` (inverse substitution) times the character `η⁻¹ det(D)`. -/
theorem line_radical_H1 (n : ℕ) :
    ∃ e : groupCohomology (lineRep n) 1 ≃ₗ[ℚ] BinaryH (n + 1),
      ∀ (t : ℤˣ) (L : GL2) (v : groupCohomology (lineRep n) 1),
        (e (lineH1LeviAction0 n t L v) : MvPolynomial (Fin 2) ℚ) =
          ((((t⁻¹ : ℤˣ) : ℤ) : ℚ) * (L.val.det : ℚ)) •
            binaryMatrixSubst (rationalBlock L⁻¹).val (e v : MvPolynomial (Fin 2) ℚ) := by
  refine ⟨latticeH1ScalarEquiv n, fun t L v => ?_⟩
  rw [lineH1LeviAction0_eq]
  have h := latticeH1ScalarEquiv_Levi n t L v
  have ht : (((t⁻¹ : ℤˣ) : ℤ) : ℚ) = (t.val : ℚ) := by
    rcases Int.units_eq_one_or t with rfl | rfl <;> norm_num
  rw [ht, map_smul, Submodule.coe_smul, h]

/-- The contraction `(α, β) ↦ zα - yβ` descends to the Lie quotient `closed pairs / exact pairs` of the line radical. -/
def lineLieMap (n : ℕ) : lineDerivativeQuotient n →ₗ[ℚ] BinaryH (n + 1) :=
  Submodule.liftQ (LinearMap.range (lineDerivativeComplex n).moduleCatToCycles)
    (scalar n) (by
      rintro _ ⟨w, rfl⟩
      exact (scalar_kernel n _).mpr ⟨w, rfl⟩)

/-- **The Lie-algebra computation of `H¹(N_L, E)` (line radical `N_L = ⟨U₁₂,U₁₃⟩`, root operators
`y∂_x, z∂_x` up to sign):** closed pairs modulo exact pairs are the binary forms of degree `n + 1` in `y, z`, by the
contraction `(α, β) ↦ zα - yβ` (which is independent of `x` on closed pairs). -/
def lineLieEquiv (n : ℕ) : lineDerivativeQuotient n ≃ₗ[ℚ] BinaryH (n + 1) :=
  LinearEquiv.ofBijective (lineLieMap n) ⟨by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' : scalar n v = 0 := hx
    obtain ⟨w, hw⟩ := (scalar_kernel n v).mp hx'
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨w, hw⟩, by
    intro J
    exact ⟨Submodule.Quotient.mk (eulerPair n J), scalar_eulerPair n J⟩⟩

/-- A binary homogeneous polynomial fixed by `x ↦ x - t y` is a multiple of `y^d`. -/
theorem binary_upper_fixed (t : ℚ) (ht : t ≠ 0) {d : ℕ} (p : BinaryH d)
    (hp : bind₁ ![X 0 - C t * X 1, X 1] (p : MvPolynomial (Fin 2) ℚ) = (p : MvPolynomial (Fin 2) ℚ)) :
    ∃ c : ℚ, (p : MvPolynomial (Fin 2) ℚ) = C c * X 1 ^ d := by
  let q : UnaryH d := ⟨(MvPolynomial.finSuccEquiv ℚ 1 (p : MvPolynomial (Fin 2) ℚ)).coeff 0,
    p.property.finSuccEquiv_coeff_isHomogeneous 0 d (by omega)⟩
  have h1 := OrdinaryFaceRadical.binary_shearStep_fixed_axis t ht p hp
  have hq := unary_homogeneous_eq d q
  refine ⟨unaryScalarEquiv d q, ?_⟩
  rw [h1]
  change rename Fin.succ (q : MvPolynomial (Fin 1) ℚ) = _
  rw [hq]
  have hm : monomial (Finsupp.single (0 : Fin 1) d) (unaryScalarEquiv d q) =
      X 0 ^ d * C (unaryScalarEquiv d q) := by
    simpa using (monomial_single_add (n := (0 : Fin 1)) (e := d) (s := 0)
      (a := unaryScalarEquiv d q))
  change rename Fin.succ (monomial (Finsupp.single (0 : Fin 1) d) (unaryScalarEquiv d q)) = _
  rw [hm]
  simp [mul_comm]

/-- A binary homogeneous polynomial fixed by `z ↦ z - t y` (second variable moved by the first) is a multiple of
`y^d`, `y` the first variable. -/
theorem binary_lower_fixed (t : ℚ) (ht : t ≠ 0) {d : ℕ} (p : BinaryH d)
    (hp : bind₁ ![X 0, X 1 - C t * X 0] (p : MvPolynomial (Fin 2) ℚ) = (p : MvPolynomial (Fin 2) ℚ)) :
    ∃ c : ℚ, (p : MvPolynomial (Fin 2) ℚ) = C c * X 0 ^ d := by
  let s : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  let p' : BinaryH d := ⟨rename s (p : MvPolynomial (Fin 2) ℚ), p.property.rename_isHomogeneous⟩
  have hp' : bind₁ ![X 0 - C t * X 1, X 1] (p' : MvPolynomial (Fin 2) ℚ) = (p' : MvPolynomial (Fin 2) ℚ) := by
    have h := congrArg (rename s) hp
    have e : (rename s).comp (bind₁ ![X 0, X 1 - C t * X 0]) =
        (bind₁ ![X 0 - C t * X 1, X 1]).comp (rename s) := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp [s]
    have h2 := DFunLike.congr_fun e (p : MvPolynomial (Fin 2) ℚ)
    simp only [AlgHom.comp_apply] at h2
    change bind₁ ![X 0 - C t * X 1, X 1] (rename s (p : MvPolynomial (Fin 2) ℚ)) = rename s (p : MvPolynomial (Fin 2) ℚ)
    rw [← h2, hp]
  obtain ⟨c, hc⟩ := binary_upper_fixed t ht p' hp'
  refine ⟨c, ?_⟩
  have h := congrArg (rename s) hc
  have hss : rename s (rename s (p : MvPolynomial (Fin 2) ℚ)) = (p : MvPolynomial (Fin 2) ℚ) := by
    rw [rename_rename]
    have : (s ∘ s) = id := by
      funext i; fin_cases i <;> simp [s]
    rw [this, rename_id_apply]
  change rename s (rename s (p : MvPolynomial (Fin 2) ℚ)) = rename s (C c * X 1 ^ d) at h
  rw [hss] at h
  rw [h]
  simp [s]


open TernaryPoly.RelativeEdgeCohomologyMatrices TernaryPoly.RadicalFirstCohomology

/-- The weight `(a₁, a₂, a₃)` of the table, restricted to `D₀ = {diag(η₁, η₂, 1)}`: the character
`diag(d₁, d₂, d₃) ↦ d₁^{a₁} d₂^{a₂} d₃^{a₃}` evaluated at `d₃ = 1`. -/
def weight (a₁ a₂ : ℤ) (ε : ℤˣ × ℤˣ) : ℚ := (ε.1.val : ℚ) ^ a₁ * (ε.2.val : ℚ) ^ a₂

/-- The diagonal Levi element `diag(η₁, η₂) ∈ GL₂(ℤ)` of the plane radical. -/
def diagGL2 (ε : ℤˣ × ℤˣ) : GL2 where
  val := !![ε.1.val, 0; 0, ε.2.val]
  inv := !![(ε.1⁻¹).val, 0; 0, (ε.2⁻¹).val]
  val_inv := by
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, ← Units.val_mul]
  inv_val := by
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, ← Units.val_mul]

/-- The diagonal Levi block `diag(η₂, 1) ∈ GL₂(ℤ)` of the line radical. -/
def diagGL2' (η : ℤˣ) : GL2 where
  val := !![η.val, 0; 0, 1]
  inv := !![(η⁻¹).val, 0; 0, 1]
  val_inv := by
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, ← Units.val_mul]
  inv_val := by
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_two, ← Units.val_mul]

open RelativeStabilizerMatrices

theorem planeElement_diagGL2 (ε : ℤˣ × ℤˣ) : planeElement (diagGL2 ε) 0 = diagonalHom ε := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeElement_val, planeMatrix, diagGL2, diagonalHom, bbElement_val, bbMatrix]

theorem lineElement_diagGL2' (ε : ℤˣ × ℤˣ) : lineElement ε.1 0 (diagGL2' ε.2) = diagonalHom ε := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineElement_val, lineMatrix, diagGL2', diagonalHom, bbElement_val, bbMatrix]

theorem planeElement_upper : planeElement binaryUpper 0 = (bbRoot 0 1).val := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [planeElement_val, planeMatrix, binaryUpper, bbRoot, rootElement, bbElement_val, bbMatrix]

theorem lineElement_lower : lineElement 1 0 (binaryLowerStep 3) = (bgRoot 1 1).val := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineElement_val, lineMatrix, binaryLowerStep, binaryLowerMatrix, bgRoot, bgElement_val, bgMatrix]

theorem unit_inv_val_rat (u : ℤˣ) : ((u⁻¹ : ℤˣ).val : ℚ) = ((u.val : ℚ))⁻¹ := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num

/-- **Table `tab:edge-weights`, type `BB`, second subquotient.** The invariants of the remaining root
`E₁₂` (the Levi element `((1 1; 0 1), 1)`) in `H¹(N_P, E)` form the line spanned by the class `v₀` of the potential
`y^{n+1}` (under `H¹(N_P, E) ≅ Sym^{n+1}(x,y)*`), and `D₀` acts on this line by `η₂^{-n-1}`: the weight
`(0, -n-1, 1)` at `d₃ = 1`. -/
theorem bb_second_weight (n : ℕ) :
    ∃ v₀ : groupCohomology (planeRep n) 1, v₀ ≠ 0 ∧
      (∀ v : groupCohomology (planeRep n) 1,
        planeH1Action n binaryUpper v = v ↔ ∃ c : ℚ, v = c • v₀) ∧
      ∀ ε : ℤˣ × ℤˣ, planeH1Action n (diagGL2 ε) v₀ = weight 0 (-((n : ℤ) + 1)) ε • v₀ := by
  obtain ⟨e, -, he⟩ := plane_radical_H1 n
  let J₀ : BinaryH (n + 1) := ⟨X 1 ^ (n + 1), by
    have h := (isHomogeneous_X ℚ (1 : Fin 2)).pow (n + 1)
    simpa using h⟩
  have hJ₀ : J₀ ≠ 0 := by
    intro h
    have := congrArg (fun p : BinaryH (n + 1) => (p : MvPolynomial (Fin 2) ℚ)) h
    exact pow_ne_zero _ (X_ne_zero (1 : Fin 2)) this
  have hup : ∀ v : groupCohomology (planeRep n) 1,
      (e (planeH1Action n binaryUpper v) : MvPolynomial (Fin 2) ℚ) =
        bind₁ ![X 0 - X 1, X 1] (e v : MvPolynomial (Fin 2) ℚ) := by
    intro v
    rw [he, binaryUpper_substitute]
  have hJfix : bind₁ ![X 0 - X 1, X 1] (J₀ : MvPolynomial (Fin 2) ℚ) = (J₀ : MvPolynomial (Fin 2) ℚ) := by
    change bind₁ ![X 0 - X 1, X 1] (X 1 ^ (n + 1) : MvPolynomial (Fin 2) ℚ) = X 1 ^ (n + 1)
    simp
  refine ⟨e.symm J₀, fun h => hJ₀ (by simpa using congrArg e h), ?_, ?_⟩
  · intro v
    constructor
    · intro hv
      have h : bind₁ ![X 0 - C (1 : ℚ) * X 1, X 1] (e v : MvPolynomial (Fin 2) ℚ) =
          (e v : MvPolynomial (Fin 2) ℚ) := by
        have h' := hup v
        rw [hv] at h'
        simpa using h'.symm
      obtain ⟨c, hc⟩ := binary_upper_fixed 1 one_ne_zero (e v) h
      refine ⟨c, ?_⟩
      apply e.injective
      apply Subtype.ext
      rw [map_smul, LinearEquiv.apply_symm_apply, Submodule.coe_smul, hc]
      change _ = c • (X 1 ^ (n + 1) : MvPolynomial (Fin 2) ℚ)
      rw [Algebra.smul_def]
      rfl
    · rintro ⟨c, rfl⟩
      have h0 : planeH1Action n binaryUpper (e.symm J₀) = e.symm J₀ := by
        apply e.injective
        apply Subtype.ext
        rw [hup, LinearEquiv.apply_symm_apply, hJfix]
      rw [map_smul, h0]
  · intro ε
    apply e.injective
    apply Subtype.ext
    rw [he, map_smul, LinearEquiv.apply_symm_apply, Submodule.coe_smul]
    change binaryMatrixSubst (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (diagGL2 ε)⁻¹).val
      (X 1 ^ (n + 1) : MvPolynomial (Fin 2) ℚ) = _ • (X 1 ^ (n + 1) : MvPolynomial (Fin 2) ℚ)
    have hv : ((diagGL2 ε)⁻¹).val = !![(ε.1⁻¹).val, 0; 0, (ε.2⁻¹).val] := rfl
    have hm : (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) (diagGL2 ε)⁻¹).val =
        (!![((ε.1⁻¹).val : ℚ), 0; 0, ((ε.2⁻¹).val : ℚ)] : Matrix (Fin 2) (Fin 2) ℚ) := by
      ext i j
      rw [Matrix.GeneralLinearGroup.map_apply]
      change (((diagGL2 ε)⁻¹).val i j : ℚ) = _
      rw [hv]
      fin_cases i <;> fin_cases j <;> simp
    rw [hm, map_pow]
    have h1 : binaryMatrixSubst (!![((ε.1⁻¹).val : ℚ), 0; 0, ((ε.2⁻¹).val : ℚ)]) (X 1) =
        C ((ε.2⁻¹).val : ℚ) * X 1 := by
      simp [binaryMatrixSubst, Fin.sum_univ_two]
    rw [h1, mul_pow, ← map_pow, Algebra.smul_def]
    congr 1
    simp only [weight, zpow_zero, one_mul, unit_inv_val_rat]
    have hn : (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hn, zpow_neg, zpow_natCast, inv_pow]
    rfl

theorem det_binaryLowerStep (k : ℤ) : (binaryLowerStep k).val.det = 1 := by
  change (binaryLowerMatrix k).det = 1
  rw [Matrix.det_fin_two]
  simp [binaryLowerMatrix]

/-- **Table `tab:edge-weights`, type `BG`, second subquotient.** The invariants of the remaining root
`3E₃₂` (the Levi element `(1, (1 0; 3 1))`) in `H¹(N_L, E)` form the line spanned by the class `v₀` of `y^{n+1}` in
`η⁻¹ det(D) Sym^{n+1}(y,z)*`, and `D₀` acts on it by the character `η₁⁻¹ η₂ · η₂^{-n-1} = η₁⁻¹ η₂^{-n}`: the weight
`(-1, -n, 1)` at `d₃ = 1`. -/
theorem bg_second_weight (n : ℕ) :
    ∃ v₀ : groupCohomology (lineRep n) 1, v₀ ≠ 0 ∧
      (∀ v : groupCohomology (lineRep n) 1,
        lineH1LeviAction0 n 1 (binaryLowerStep 3) v = v ↔ ∃ c : ℚ, v = c • v₀) ∧
      ∀ ε : ℤˣ × ℤˣ, lineH1LeviAction0 n ε.1 (diagGL2' ε.2) v₀ = weight (-1) (-(n : ℤ)) ε • v₀ := by
  obtain ⟨e, he⟩ := line_radical_H1 n
  let J₀ : BinaryH (n + 1) := ⟨X 0 ^ (n + 1), by
    have h := (isHomogeneous_X ℚ (0 : Fin 2)).pow (n + 1)
    simpa using h⟩
  have hJ₀ : J₀ ≠ 0 := by
    intro h
    have := congrArg (fun p : BinaryH (n + 1) => (p : MvPolynomial (Fin 2) ℚ)) h
    exact pow_ne_zero _ (X_ne_zero (0 : Fin 2)) this
  have hlow : ∀ v : groupCohomology (lineRep n) 1,
      (e (lineH1LeviAction0 n 1 (binaryLowerStep 3) v) : MvPolynomial (Fin 2) ℚ) =
        bind₁ ![X 0, X 1 - C (3 : ℚ) * X 0] (e v : MvPolynomial (Fin 2) ℚ) := by
    intro v
    rw [he]
    have h1 : ((((1 : ℤˣ)⁻¹ : ℤˣ) : ℤ) : ℚ) * ((binaryLowerStep 3).val.det : ℚ) = 1 := by
      rw [det_binaryLowerStep]; simp
    rw [h1, one_smul]
    have h2 := binaryLowerStep_substitute 3
    simp only [rationalBlock]
    rw [h2]
    simp
  have hJfix : bind₁ ![X 0, X 1 - C (3 : ℚ) * X 0] (J₀ : MvPolynomial (Fin 2) ℚ) =
      (J₀ : MvPolynomial (Fin 2) ℚ) := by
    change bind₁ ![X 0, X 1 - C (3 : ℚ) * X 0] (X 0 ^ (n + 1) : MvPolynomial (Fin 2) ℚ) = X 0 ^ (n + 1)
    simp
  refine ⟨e.symm J₀, fun h => hJ₀ (by simpa using congrArg e h), ?_, ?_⟩
  · intro v
    constructor
    · intro hv
      have h : bind₁ ![X 0, X 1 - C (3 : ℚ) * X 0] (e v : MvPolynomial (Fin 2) ℚ) =
          (e v : MvPolynomial (Fin 2) ℚ) := by
        have h' := hlow v
        rw [hv] at h'
        exact h'.symm
      obtain ⟨c, hc⟩ := binary_lower_fixed 3 (by norm_num) (e v) h
      refine ⟨c, ?_⟩
      apply e.injective
      apply Subtype.ext
      rw [map_smul, LinearEquiv.apply_symm_apply, Submodule.coe_smul, hc]
      change _ = c • (X 0 ^ (n + 1) : MvPolynomial (Fin 2) ℚ)
      rw [Algebra.smul_def]
      rfl
    · rintro ⟨c, rfl⟩
      have h0 : lineH1LeviAction0 n 1 (binaryLowerStep 3) (e.symm J₀) = e.symm J₀ := by
        apply e.injective
        apply Subtype.ext
        rw [hlow, LinearEquiv.apply_symm_apply, hJfix]
      rw [map_smul, h0]
  · intro ε
    apply e.injective
    apply Subtype.ext
    rw [he, map_smul, LinearEquiv.apply_symm_apply, Submodule.coe_smul]
    change _ • binaryMatrixSubst (rationalBlock (diagGL2' ε.2)⁻¹).val (X 0 ^ (n + 1) : MvPolynomial (Fin 2) ℚ) =
      _ • (X 0 ^ (n + 1) : MvPolynomial (Fin 2) ℚ)
    have hdet : ((diagGL2' ε.2).val.det : ℚ) = (ε.2.val : ℚ) := by
      change ((Matrix.det !![ε.2.val, 0; 0, 1] : ℤ) : ℚ) = _
      rw [Matrix.det_fin_two_of]; simp
    have hv : ((diagGL2' ε.2)⁻¹).val = !![(ε.2⁻¹).val, 0; 0, 1] := rfl
    have hm : (rationalBlock (diagGL2' ε.2)⁻¹).val =
        (!![((ε.2⁻¹).val : ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) := by
      ext i j
      change (((diagGL2' ε.2)⁻¹).val i j : ℚ) = _
      rw [hv]
      fin_cases i <;> fin_cases j <;> simp
    rw [hm, map_pow]
    have h1 : binaryMatrixSubst (!![((ε.2⁻¹).val : ℚ), 0; 0, 1]) (X 0) =
        C ((ε.2⁻¹).val : ℚ) * X 0 := by
      simp [binaryMatrixSubst, Fin.sum_univ_two]
    rw [h1, mul_pow, ← map_pow, hdet, Algebra.smul_def, Algebra.smul_def, MvPolynomial.algebraMap_eq,
      ← mul_assoc, ← map_mul]
    congr 2
    have h1' : ((ε.1.val : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ε.1.ne_zero
    have h2' : ((ε.2.val : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ε.2.ne_zero
    simp only [weight, unit_inv_val_rat, inv_pow, zpow_neg, zpow_natCast]
    field_simp
    ring

open TernaryPoly.LatticeFirstCohomology TernaryPoly.RelativeEdgeCohomologyPolynomials in
/-- `z^n` as an element of the coefficient space `E`. -/
def zPow (n : ℕ) : H n := ⟨X 2 ^ n, by
  have h := (isHomogeneous_X ℚ (2 : Fin 3)).pow n
  simpa using h⟩

open TernaryPoly.LatticeFirstCohomology TernaryPoly.RelativeEdgeCohomologyPolynomials in
theorem plane_fixed_of_generators (n : ℕ) (v : H n) (h0 : (planeRep n).ρ first v = v)
    (h1 : (planeRep n).ρ second v = v) (g : Lattice) : (planeRep n).ρ g v = v := by
  have h := cocycle_eq_zero_of_generators (planeRep n) (coboundary (planeRep n) v)
    (sub_eq_zero.mpr h0) (sub_eq_zero.mpr h1)
  exact sub_eq_zero.mp (congrArg (fun c : cocycles₁ (planeRep n) => c g) h)

open TernaryPoly.RelativeEdgeCohomologyPolynomials in
/-- A homogeneous ternary polynomial independent of `x` and `y` is a multiple of `z^n`. -/
theorem homogeneous_in_z (n : ℕ) (p : Poly) (hp : p.IsHomogeneous n) (ex0 : erase 0 p = p)
    (ex1 : erase 1 p = p) : ∃ c : ℚ, p = c • X 2 ^ n := by
  let ψ : Poly →ₐ[ℚ] MvPolynomial (Fin 1) ℚ := bind₁ ![0, 0, X 0]
  have hψ : rename (fun _ : Fin 1 => (2 : Fin 3)) (ψ p) = p := by
    have hcomp : (rename (fun _ : Fin 1 => (2 : Fin 3))).comp ψ = (erase 0).comp (erase 1) := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp [ψ]
    have := DFunLike.congr_fun hcomp p
    simp only [AlgHom.comp_apply] at this
    rw [this, ex1, ex0]
  have hψh : (ψ p).IsHomogeneous n := by
    apply isHomogeneous_bind₁_linear hp
    intro i
    fin_cases i
    · exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_zero _ _ _
    · exact isHomogeneous_X ℚ 0
  have hu := unary_homogeneous_eq n ⟨ψ p, hψh⟩
  set c : ℚ := (ψ p).coeff (Finsupp.single (0 : Fin 1) n) with hc
  have hu' : ψ p = monomial (Finsupp.single (0 : Fin 1) n) c := by rw [hc]; exact hu
  refine ⟨c, ?_⟩
  rw [← hψ, hu', rename_monomial, Finsupp.mapDomain_single, X_pow_eq_monomial, smul_monomial,
    smul_eq_mul, mul_one]

open TernaryPoly.RelativeEdgeCohomologyPolynomials in
/-- The invariants of the plane radical on `E = Sym^n((ℚ³)*)` are the line spanned by `z^n`. -/
theorem planeRadical_invariants (n : ℕ) (p : H n) :
    (∀ g, (planeRep n).ρ g p = p) ↔ ∃ c : ℚ, p = c • zPow n := by
  constructor
  · intro h
    have h0 : shear 0 2 (p : Poly) = p := by
      have := h first
      rw [planeRep_first] at this
      exact congrArg Subtype.val this
    have h1 : shear 1 2 (p : Poly) = p := by
      have := h second
      rw [planeRep_second] at this
      exact congrArg Subtype.val this
    have ex0 : erase 0 (p : Poly) = p := shear_fixed_erase 1 p h0
    have ex1 : erase 1 (p : Poly) = p := by
      let σ : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
      have e1 : σ 1 = 0 := Equiv.swap_apply_right _ _
      have e2 : σ 2 = 2 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      have hσ : shear 0 2 (rename σ (p : Poly)) = rename σ (p : Poly) := by
        have h' := congrArg (rename σ) h1
        rw [← RelativeEdgeCohomologyPolynomials.shearStep_one, rename_shearStep, e1, e2,
          RelativeEdgeCohomologyPolynomials.shearStep_one] at h'
        exact h'
      have hx := shear_fixed_erase 1 (rename σ (p : Poly)) hσ
      apply rename_injective σ σ.injective
      rw [rename_erase, e1, hx]
    obtain ⟨c, hc⟩ := homogeneous_in_z n p p.property ex0 ex1
    exact ⟨c, Subtype.ext hc⟩
  · rintro ⟨c, rfl⟩ g
    have hz : ∀ i j : Fin 3, i ≠ 2 → shear i j (X 2 ^ n : Poly) = X 2 ^ n := by
      intro i j hi
      simp [hi.symm]
    rw [map_smul]
    congr 1
    apply plane_fixed_of_generators
    · rw [planeRep_first]
      apply Subtype.ext
      exact hz 0 2 (by decide)
    · rw [planeRep_second]
      apply Subtype.ext
      exact hz 1 2 (by decide)

theorem zPow_diagonal (n : ℕ) (ε : ℤˣ × ℤˣ) :
    PolynomialGLAction.integralAction n 0 (diagonalHom ε) (zPow n) = zPow n := by
  apply Subtype.ext
  rw [integralAction_diagonal]
  change diagonalSubst (unitScalar ε.1⁻¹) (unitScalar ε.2⁻¹) (X 2 ^ n : Poly) = X 2 ^ n
  simp [diagonalSubst]

/-- **Table `tab:edge-weights`, type `BB`, first subquotient.** With `N = N_P` and the remaining root
`E₁₂`: the invariants `E^{N_P}` are the line `ℚ z^n`; the diagonal group `D₀` fixes `z^n` (the determinant exponent is
`0` and `d₃ = 1`); conjugation by `diag(η₁, η₂, 1)` scales the root group `⟨E₁₂⟩` by `η₁ η₂⁻¹`, so on
`H¹(⟨E₁₂⟩, E^{N_P}) = Hom(⟨E₁₂⟩, ℚ z^n)` the group acts through `(η₁ η₂⁻¹)⁻¹ = η₁⁻¹ η₂`: the weight `(-1, 1, -n)` at
`d₃ = 1`. -/
theorem bb_first_weight (n : ℕ) :
    (∀ p : H n, (∀ g, (planeRep n).ρ g p = p) ↔ ∃ c : ℚ, p = c • zPow n) ∧
    (∀ ε : ℤˣ × ℤˣ, PolynomialGLAction.integralAction n 0 (diagonalHom ε) (zPow n) = zPow n) ∧
    ∀ ε : ℤˣ × ℤˣ,
      (diagonalHom ε * (bbRoot 0 1).val * (diagonalHom ε)⁻¹ = (bbRoot 0 (rootScale ε 0)).val) ∧
      ((rootScale ε 0 : ℤ) : ℚ)⁻¹ = weight (-1) 1 ε := by
  refine ⟨planeRadical_invariants n, zPow_diagonal n, fun ε => ⟨?_, ?_⟩⟩
  · have h := diagonal_root_conjugate ε 0 1
    simpa [bbRoot, mul_one] using h
  · rcases Int.units_eq_one_or ε.1 with h1 | h1 <;> rcases Int.units_eq_one_or ε.2 with h2 | h2 <;>
      simp [rootScale, weight, h1, h2]

open TernaryPoly.RelativeEdgeCohomologyPolynomials in
/-- The invariants of the line radical on `E = Sym^n((ℚ³)*)` are the polynomials independent of `x`, i.e.
`ℚ[y,z]_n`. -/
theorem lineRadical_invariants (n : ℕ) (p : H n) :
    (∀ g, (lineRep n).ρ g p = p) ↔ erase 0 (p : Poly) = p := by
  constructor
  · intro h
    have h0 : shear 0 1 (p : Poly) = p := by
      have := h first
      rw [lineRep_first] at this
      exact congrArg Subtype.val this
    exact shear_fixed_erase 0 p h0
  · intro hp g
    apply SymmetricLineCohomology.fixed_of_generators
    · rw [lineRep_first]
      apply Subtype.ext
      change shear 0 1 (p : Poly) = p
      rw [← RelativeEdgeCohomologyPolynomials.shearStep_one]
      exact first_shearStep_fixed 1 1 p hp
    · rw [lineRep_second]
      apply Subtype.ext
      change shear 0 2 (p : Poly) = p
      rw [← RelativeEdgeCohomologyPolynomials.shearStep_one]
      exact first_shearStep_fixed 2 1 p hp

open TernaryPoly.RelativeEdgeCohomologyPolynomials in
theorem diagonal_bgRoot_commute (ε : ℤˣ × ℤˣ) (t : ℤ) :
    diagonalHom ε * (bgRoot 1 t).val = (bgRoot 1 (ε.2.val * t)).val * diagonalHom ε := by
  rcases ε with ⟨a, b⟩
  rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl <;>
    apply Units.ext <;> rw [Units.val_mul, Units.val_mul] <;> ext i j <;>
    rw [Matrix.mul_apply, Matrix.mul_apply] <;> fin_cases i <;> fin_cases j <;>
    simp [diagonalHom, bgRoot, bgElement_val, bgMatrix, bbElement_val, bbMatrix, Fin.sum_univ_three]

open TernaryPoly.RelativeEdgeCohomologyPolynomials TernaryPoly.RelativeEdgeCohomologyActions in
/-- **Table `tab:edge-weights`, type `BG`, first subquotient.** With `N = N_L` and the remaining root
`3E₃₂`: the invariants `E^{N_L}` are `ℚ[y,z]_n` (polynomials without `x`); their coinvariants under `3E₃₂` (the shear
`z ↦ z - 3y`, i.e. `-3y∂_z` to first order) are the line spanned by `z^n` (`z^n` is not in the image of `shear - 1`, and
every invariant is a multiple of `z^n` modulo the image); `D₀` fixes `z^n`; conjugation by `diag(η₁, η₂, 1)` scales the
root `3E₃₂` by `η₂` (`d₃/d₂`), whose dual `η₂⁻¹ = η₂` is the factor of
`H¹(⟨3E₃₂⟩, E^{N_L}) = (E^{N_L})_{⟨3E₃₂⟩} ⊗ (root)*`: the weight `(0, 1, -n-1)` at `d₃ = 1`. -/
theorem bg_first_weight (n : ℕ) :
    (∀ p : H n, (∀ g, (lineRep n).ρ g p = p) ↔ erase 0 (p : Poly) = p) ∧
    (∀ p : H n, erase 0 (p : Poly) = p → ∃ (c : ℚ) (v : H n), erase 0 (v : Poly) = v ∧
      (p : Poly) = c • (X 2 ^ n : Poly) + (((bgRep n).ρ (bgRoot 1 1) v : H n) - v : H n)) ∧
    (∀ (c : ℚ) (v : H n), (c • X 2 ^ n : Poly) = (((bgRep n).ρ (bgRoot 1 1) v : H n) - v : H n) → c = 0) ∧
    (∀ ε : ℤˣ × ℤˣ, PolynomialGLAction.integralAction n 0 (diagonalHom ε) (zPow n) = zPow n) ∧
    ∀ ε : ℤˣ × ℤˣ,
      (diagonalHom ε * (bgRoot 1 1).val = (bgRoot 1 ε.2.val).val * diagonalHom ε) ∧
      ((ε.2.val : ℤ) : ℚ)⁻¹ = weight 0 1 ε := by
  refine ⟨lineRadical_invariants n, ?_, ?_, zPow_diagonal n, fun ε => ⟨?_, ?_⟩⟩
  · intro p hp
    have e01 : erase 1 (p : Poly) = erase 0 (erase 1 (p : Poly)) := by
      rw [erase_erase, hp]
    have hp1h : (erase 1 (p : Poly)).IsHomogeneous n := RadicalCoinvariantAlgebra.erase_homogeneous 1 p.property
    obtain ⟨c, hc⟩ := homogeneous_in_z n (erase 1 (p : Poly)) hp1h e01.symm (erase_idempotent 1 _)
    have hz : (X 2 ^ n : Poly) = erase 1 (X 2 ^ n) := by simp
    have hzh : (X 2 ^ n : Poly).IsHomogeneous n := by
      have h := (isHomogeneous_X ℚ (2 : Fin 3)).pow n
      simpa using h
    have hq : ((p : Poly) - c • X 2 ^ n).IsHomogeneous n := p.property.sub (by simpa [smul_eq_C_mul] using hzh.C_mul c)
    have hq0 : erase 1 ((p : Poly) - c • X 2 ^ n) = 0 := by
      rw [map_sub, hc, map_smul, ← hz, sub_self]
    have hqe : erase 0 ((p : Poly) - c • X 2 ^ n) = (p : Poly) - c • X 2 ^ n := by
      rw [map_sub, map_smul, hp]
      simp
    obtain ⟨v, hv, hve, hvs⟩ := exists_independent_shearStep 2 1 (by decide) (by decide) (by decide)
      3 (by norm_num) _ hq hq0 hqe
    refine ⟨c, ⟨v, hv⟩, hve, ?_⟩
    have hb := bg_action_coe n 1 ⟨v, hv⟩
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hb
    rw [Submodule.coe_sub, hb]
    change (p : Poly) = c • (X 2 ^ n : Poly) + (shearStep 2 1 3 v - v)
    rw [hvs]
    abel
  · intro c v h
    have h' := congrArg (erase 1) h
    have hb := bg_action_coe n 1 v
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hb
    rw [Submodule.coe_sub, hb] at h'
    rw [map_sub, erase_shearStep 2 1 (by decide), sub_self, map_smul] at h'
    simp only [erase_X, map_pow] at h'
    simpa using h'
  · simpa using diagonal_bgRoot_commute ε 1
  · rcases Int.units_eq_one_or ε.2 with h2 | h2 <;> simp [weight, h2]

/-- **Parity of the weights (caption of `tab:edge-weights`).** For even `n`, each of the four weights has a
nontrivial sign character on `D₀`: it takes the value `-1` on some `diag(η₁, η₂, 1)`. With `H¹(H_BB,E)` and `H¹(H_BG,E)`
the `D₀`-invariants of the edge cohomology (exact averaging), this is why they vanish; the library proves that vanishing
directly (`Statements.AlternatingEven.edge_stabilizer_H1_vanishing`). -/
theorem edge_weights_nontrivial (n : ℕ) (hn : Even n) :
    (∃ ε : ℤˣ × ℤˣ, weight (-1) 1 ε = -1) ∧
    (∃ ε : ℤˣ × ℤˣ, weight 0 (-((n : ℤ) + 1)) ε = -1) ∧
    (∃ ε : ℤˣ × ℤˣ, weight 0 1 ε = -1) ∧
    (∃ ε : ℤˣ × ℤˣ, weight (-1) (-(n : ℤ)) ε = -1) := by
  obtain ⟨m, rfl⟩ := hn
  refine ⟨⟨(-1, 1), ?_⟩, ⟨(1, -1), ?_⟩, ⟨(1, -1), ?_⟩, ⟨(-1, 1), ?_⟩⟩
  · simp [weight]
  · have h : (-(((m + m : ℕ) : ℤ) + 1)) = -((2 * m + 1 : ℕ) : ℤ) := by push_cast; ring
    simp only [weight, h, zpow_neg, zpow_natCast]
    rw [pow_succ, pow_mul]
    simp
  · simp [weight]
  · simp [weight]

/-- The cocycle equation of the Lie algebra complex of the plane radical: for the root operators
`z∂_x, z∂_y`, a pair `(a, b)` is closed iff `a_y = b_x`. -/
theorem plane_lie_cocycle_equation (n : ℕ) (a b : H n) :
    planeDerivativeCurl n ![a, b] = 0 ↔ pderiv 1 (a : Poly) = pderiv 0 (b : Poly) := by
  constructor
  · intro h
    obtain ⟨F, -, ha, hb⟩ := (plane_lie_closed_iff_gradient n a b).mp h
    rw [← ha, ← hb, MultivariateIntegral.pderiv_commute 0 1]
  · intro h
    apply Subtype.ext
    rw [planeDerivativeCurl_coe]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Submodule.coe_zero]
    rw [h]
    ring

/-- The comparison of Lie and group cohomology for the plane radical (the abelian case of the nilmanifold
theorem, as an explicit Todd isomorphism): `H¹(N_P, E)` is the quotient of the closed pairs of root derivatives by the exact
pairs. -/
alias plane_group_lie_comparison := TernaryPoly.RadicalFirstCohomology.planeH1DerivativeQuotientIso

/-- The same for the line radical. -/
alias line_group_lie_comparison := TernaryPoly.RadicalFirstCohomology.lineH1DerivativeQuotientIso

/-- On a closed pair of the line radical, the contraction `zα - yβ` is independent of `x` (dual root
operators, after the renaming `x ↔ z`). -/
alias line_lie_contraction_independent := TernaryPoly.SymmetricLineCohomology.contraction_independent

/-- A closed pair of the line radical is exact iff its contraction is zero (the binary form of degree `n + 1` vanishes). -/
alias line_lie_exact_iff := TernaryPoly.SymmetricLineCohomology.scalar_kernel

/-- The contraction is onto the binary forms of degree `n + 1` (Euler section). -/
alias line_lie_surjective := TernaryPoly.SymmetricLineCohomology.scalar_surjective

end TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables
