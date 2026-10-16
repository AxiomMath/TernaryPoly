module

public import TernaryPeriodPolynomials.GroupCohomology.EdgeCohomology.TwistSubquotients
public import TernaryPeriodPolynomials.GroupCohomology.EdgeCohomology.Transport
public import TernaryPeriodPolynomials.GroupCohomology.Radical.TopCohomologyPlane
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyPlane
public import TernaryPeriodPolynomials.BoundaryComparison.RadicalCohomologyTables
public import TernaryPeriodPolynomials.GroupCohomology.Radical.TopCohomologyLine
public import TernaryPeriodPolynomials.GroupCohomology.Radical.FirstCohomologyLine
public import TernaryPeriodPolynomials.SymmetricSolution.LineCohomology.Levi

@[expose] public section


/-!
# `tab:edge-weights`: the exact sequence of the edge stabilizers and its two subquotients

Formalized by Claude Sonnet 5.5.

Paper: "For either edge radical, extend a rank-two radical by its remaining cyclic root. The exact sequence
`0 → H¹(ℤ, E^N) → H¹(N_edge, E) → H¹(N, E)^ℤ → 0` is equivariant for `D₀ = {diag(η₁, η₂, 1)}`", and `tab:edge-weights`: the weights of
the two one-dimensional subquotients are `(-1, 1, -n)` and `(0, -n-1, 1)` for `BB`, `(0, 1, -n-1)` and `(-1, -n, 1)` for `BG`.

**Setting.**  `E = Sym^n((ℚ³)*)` (determinant exponent `0`).  The unipotent edge groups are the semidirect products
`N_edge^{BB} = N_P ⋊ ⟨E₁₂⟩ = ⟨U₁₂, U₁₃, U₂₃⟩` (`GBB`, `phiBB`, embedded in `GL₃(ℤ)` by `eBB`) and `N_edge^{BG} = N_L ⋊ ⟨3E₃₂⟩` (`GBG`, `phiBG`,
`eBG`), with `N = ℤ²` the lattice of the vertex radical; `ABB n`, `ABG n` are the restrictions of `E`.  `D₀` acts on `N_edge` by
conjugation with `diag(η₁, η₂, 1)⁻¹` (`twistBB`, `twistBG`: an automorphism `ψ ⋊ (q ↦ q^s)`, `s = ±1`, together with the coefficient map
`E → E`, `p ↦ diag p`).

**Results.**
* `bb_edge_subquotients`, `bg_edge_subquotients`: `H¹(N_edge, E)` has a basis `x₁, x₂`; `infl : H¹(ℤ, E^N) → H¹(N_edge, E)` is injective with image
  `ℚ x₁ = ker (resp)` (so `H¹(ℤ, E^N)` is the first one-dimensional subquotient), the image of `resp : H¹(N_edge, E) → H¹(N, E)` is the line of
  the `ℤ`-invariants of `H¹(N, E)` (identified, through the Levi-equivariant isomorphisms of `Statements.RadicalCohomologyTables`, with the invariants of the
  remaining root in `Sym^{n+1}`), so the second subquotient is `H¹(N, E)^ℤ`; and the weights are exactly those of the table: `D₀` acts on `x₁` by
  `weight (-1) 1` (`BB`) resp. `weight 0 1` (`BG`), and on `x₂` modulo `x₁` by `weight 0 (-(n+1))` resp. `weight (-1) (-n)`.
* The general mechanism is in `Proofs/EdgeCohomology`: the exactness of `0 → H¹(Q, A^N) → H¹(N ⋊ Q, A) → H¹(N, A)^Q → 0` for `Q = ℤ`
  (`SemidirectSequence`, built on `TernaryPoly.LowDegreeHochschildSerre`) and the action of the twist on the two subquotients (`TwistSubquotients`).

For even `n` all four weights are nontrivial sign characters (`RadicalCohomologyTables.edge_weights_nontrivial`), so `H¹(N_edge, E)^{D₀} = 0`, the input of the
paper's "exact averaging" step.
-/

open TernaryPoly

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.EdgeSubquotients

open CategoryTheory groupCohomology TernaryPoly.LowDegreeHochschildSerre
open TernaryPeriodPolynomials.Argument.EdgeCohomology
open TernaryPoly.LatticeTopCohomology TernaryPoly.RadicalFirstCohomologyLattice
open RelativeStabilizerParameters RelativeStabilizerMatrices ModThreeGoodAction TernaryPoly.RadicalCoinvariantAlgebra

/-- Conjugation by the root `E₁₂` on the plane lattice `⟨U₁₃, U₂₃⟩`: `(a, b) ↦ (a + q b, b)`. -/
def phiBB : Multiplicative ℤ →* MulAut Lattice where
  toFun q := matrixLattice (TernaryPoly.OrdinaryFaceRadical.binaryUpperStep q.toAdd)
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Multiplicative.toAdd.injective
    simp [TernaryPoly.OrdinaryFaceRadical.binaryUpperStep, TernaryPoly.OrdinaryFaceRadical.binaryUpperMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  map_mul' q r := by
    apply MulEquiv.ext
    intro g
    apply Multiplicative.toAdd.injective
    simp [TernaryPoly.OrdinaryFaceRadical.binaryUpperStep, TernaryPoly.OrdinaryFaceRadical.binaryUpperMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

/-- The root group `⟨E₁₂⟩` as a homomorphism from `ℤ`. -/
def rootBB : Multiplicative ℤ →* IntegralGL where
  toFun q := rootElement 0 q.toAdd
  map_one' := rootElement_zero 0
  map_mul' _ _ := (rootElement_mul 0 _ _).symm

theorem phiBB_apply (q : Multiplicative ℤ) (g : Lattice) :
    (phiBB q g).toAdd = (g.toAdd.1 + q.toAdd * g.toAdd.2, g.toAdd.2) := by
  simp [phiBB, TernaryPoly.OrdinaryFaceRadical.binaryUpperStep, TernaryPoly.OrdinaryFaceRadical.binaryUpperMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem rootBB_mul_planeHom (q : Multiplicative ℤ) (g : Lattice) :
    rootBB q * planeHom g = planeHom (phiBB q g) * rootBB q := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have h := phiBB_apply q g
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [rootBB, rootElement, planeHom, planeElement_val, planeMatrix, bbElement_val, bbMatrix,
      Fin.sum_univ_three, h]

theorem commBB (q : Multiplicative ℤ) :
    planeHom.comp (phiBB q).toMonoidHom = (MulAut.conj (rootBB q)).toMonoidHom.comp planeHom := by
  apply MonoidHom.ext
  intro g
  change planeHom (phiBB q g) = rootBB q * planeHom g * (rootBB q)⁻¹
  rw [rootBB_mul_planeHom, mul_inv_cancel_right]

/-- The edge group `N_P ⋊ ⟨E₁₂⟩ ≅ ⟨U₁₂, U₁₃, U₂₃⟩` as an abstract semidirect product. -/
abbrev GBB := Lattice ⋊[phiBB] Multiplicative ℤ

/-- The embedding of the semidirect product into `GL₃(ℤ)`. -/
def eBB : GBB →* IntegralGL := SemidirectProduct.lift planeHom rootBB commBB

/-- The coefficient representation `E = Sym^n((ℚ³)*)` restricted to the edge group. -/
def ABB (n : ℕ) : Rep.{0} ℚ GBB := Rep.of ((PolynomialGLAction.integralAction n 0).comp eBB)

theorem ABB_nIn (n : ℕ) (m : Lattice) :
    (ABB n).ρ (nIn phiBB m) = PolynomialGLAction.integralAction n 0 (planeHom m) := by
  change PolynomialGLAction.integralAction n 0 (eBB (nIn phiBB m)) = _
  rw [show eBB (nIn phiBB m) = planeHom m from SemidirectProduct.lift_inl _ _ _ _]

theorem ABB_qIn (n : ℕ) (q : Multiplicative ℤ) :
    (ABB n).ρ (qIn phiBB q) = PolynomialGLAction.integralAction n 0 (rootElement 0 q.toAdd) := by
  change PolynomialGLAction.integralAction n 0 (eBB (qIn phiBB q)) = _
  rw [show eBB (qIn phiBB q) = rootBB q from SemidirectProduct.lift_inr _ _ _ _]
  rfl

section TwistBB

open TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables (diagGL2)

/-- Conjugation of the plane lattice by `diag(η₁, η₂)⁻¹`. -/
def psiBB (ε : ℤˣ × ℤˣ) : Lattice →* Lattice := (matrixLattice (diagGL2 ε)⁻¹).toMonoidHom

theorem psiBB_apply (ε : ℤˣ × ℤˣ) (g : Lattice) :
    (psiBB ε g).toAdd = ((ε.1⁻¹).val * g.toAdd.1, (ε.2⁻¹).val * g.toAdd.2) := by
  have hv : ((diagGL2 ε)⁻¹).val = !![(ε.1⁻¹).val, 0; 0, (ε.2⁻¹).val] := rfl
  change (matrixLattice (diagGL2 ε)⁻¹ g).toAdd = _
  rw [matrixLattice_coordinates, hv]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The exponent by which conjugation by `diag(η₁, η₂, 1)⁻¹` scales the root `E₁₂`: `η₁ η₂` (`= η₁⁻¹ η₂`). -/
def sBB (ε : ℤˣ × ℤˣ) : ℤ := ε.1.val * ε.2.val

theorem sBB_cases (ε : ℤˣ × ℤˣ) : sBB ε = 1 ∨ sBB ε = -1 := by
  rcases Int.units_eq_one_or ε.1 with h1 | h1 <;> rcases Int.units_eq_one_or ε.2 with h2 | h2 <;>
    simp [sBB, h1, h2]

theorem psiBB_compat (ε : ℤˣ × ℤˣ) (q : Multiplicative ℤ) :
    (psiBB ε).comp (phiBB q).toMonoidHom =
      (phiBB (zpowGroupHom (sBB ε) q)).toMonoidHom.comp (psiBB ε) := by
  apply MonoidHom.ext
  intro g
  apply Multiplicative.toAdd.injective
  change (psiBB ε (phiBB q g)).toAdd = (phiBB (zpowGroupHom (sBB ε) q) (psiBB ε g)).toAdd
  rw [psiBB_apply, phiBB_apply, phiBB_apply, psiBB_apply]
  rcases Int.units_eq_one_or ε.1 with h1 | h1 <;> rcases Int.units_eq_one_or ε.2 with h2 | h2 <;>
    simp [sBB, h1, h2] <;> ring

theorem diag_planeHom (ε : ℤˣ × ℤˣ) (m : Lattice) :
    diagonalHom ε * planeHom (psiBB ε m) = planeHom m * diagonalHom ε := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have h := psiBB_apply ε m
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rcases Int.units_eq_one_or ε.1 with h1 | h1 <;> rcases Int.units_eq_one_or ε.2 with h2 | h2 <;>
    fin_cases i <;> fin_cases j <;>
    simp [diagonalHom, planeHom, planeElement_val, planeMatrix, bbElement_val, bbMatrix, Fin.sum_univ_three,
      h, h1, h2]

theorem diag_rootBB (ε : ℤˣ × ℤˣ) (q : Multiplicative ℤ) :
    diagonalHom ε * rootBB (zpowGroupHom (sBB ε) q) = rootBB q * diagonalHom ε := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rcases Int.units_eq_one_or ε.1 with h1 | h1 <;> rcases Int.units_eq_one_or ε.2 with h2 | h2 <;>
    fin_cases i <;> fin_cases j <;>
    simp [diagonalHom, rootBB, rootElement, bbElement_val, bbMatrix, Fin.sum_univ_three, sBB, h1, h2]

end TwistBB

section TwistBB3

/-- The automorphism of the edge group. -/
def sigmaBB (ε : ℤˣ × ℤˣ) : GBB →* GBB :=
  SemidirectProduct.map (psiBB ε) (zpowGroupHom (sBB ε)) (psiBB_compat ε)

theorem eBB_sigma (ε : ℤˣ × ℤˣ) (g : GBB) :
    diagonalHom ε * eBB (sigmaBB ε g) = eBB g * diagonalHom ε := by
  have hl : ∀ m : Lattice, diagonalHom ε * eBB (sigmaBB ε (nIn phiBB m)) = eBB (nIn phiBB m) * diagonalHom ε := by
    intro m
    unfold sigmaBB
    rw [SemidirectProduct.map_inl]
    change diagonalHom ε * eBB (nIn phiBB (psiBB ε m)) = eBB (nIn phiBB m) * _
    rw [show eBB (nIn phiBB (psiBB ε m)) = planeHom (psiBB ε m) from SemidirectProduct.lift_inl _ _ _ _,
      show eBB (nIn phiBB m) = planeHom m from SemidirectProduct.lift_inl _ _ _ _]
    exact diag_planeHom ε m
  have hr : ∀ q : Multiplicative ℤ, diagonalHom ε * eBB (sigmaBB ε (qIn phiBB q)) = eBB (qIn phiBB q) * diagonalHom ε := by
    intro q
    unfold sigmaBB
    rw [SemidirectProduct.map_inr]
    change diagonalHom ε * eBB (qIn phiBB (zpowGroupHom (sBB ε) q)) = eBB (qIn phiBB q) * _
    rw [show eBB (qIn phiBB (zpowGroupHom (sBB ε) q)) = rootBB (zpowGroupHom (sBB ε) q) from
        SemidirectProduct.lift_inr _ _ _ _,
      show eBB (qIn phiBB q) = rootBB q from SemidirectProduct.lift_inr _ _ _ _]
    exact diag_rootBB ε q
  have hg : g = nIn phiBB g.left * qIn phiBB g.right := (SemidirectProduct.inl_left_mul_inr_right g).symm
  rw [hg, map_mul, map_mul, map_mul]
  calc diagonalHom ε * (eBB (sigmaBB ε (nIn phiBB g.left)) * eBB (sigmaBB ε (qIn phiBB g.right)))
      = (diagonalHom ε * eBB (sigmaBB ε (nIn phiBB g.left))) * eBB (sigmaBB ε (qIn phiBB g.right)) := by
        rw [mul_assoc]
    _ = eBB (nIn phiBB g.left) * diagonalHom ε * eBB (sigmaBB ε (qIn phiBB g.right)) := by rw [hl]
    _ = eBB (nIn phiBB g.left) * (diagonalHom ε * eBB (sigmaBB ε (qIn phiBB g.right))) := by rw [mul_assoc]
    _ = _ := by rw [hr, mul_assoc]

/-- The twist of the edge group `BB` by `diag(η₁, η₂, 1)`. -/
def twistBB (n : ℕ) (ε : ℤˣ × ℤˣ) : Twist phiBB (ABB n) where
  ψ := psiBB ε
  s := sBB ε
  hs := sBB_cases ε
  hψ := (matrixLattice (TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables.diagGL2 ε)⁻¹).surjective
  compat := psiBB_compat ε
  T := PolynomialGLAction.integralAction n 0 (diagonalHom ε)
  hT := fun g v => by
    have hmat : PolynomialGLAction.integralAction n 0 (diagonalHom ε) *
        PolynomialGLAction.integralAction n 0 (eBB (sigmaBB ε g)) =
        PolynomialGLAction.integralAction n 0 (eBB g) *
        PolynomialGLAction.integralAction n 0 (diagonalHom ε) := by
      rw [← map_mul, ← map_mul, eBB_sigma]
    exact LinearMap.congr_fun hmat v

end TwistBB3

attribute [irreducible] eBB

section Theta

theorem radical_rho_BB0 (n : ℕ) (m : Lattice) :
    (radicalRep phiBB (ABB n)).ρ m = (ABB n).ρ (nIn phiBB m) := rfl

theorem planeRep_rho (n : ℕ) (m : Lattice) :
    (planeRep n).ρ m = PolynomialGLAction.integralAction n 0 (planeHom m) := rfl

theorem radical_rho_BB1 (n : ℕ) (m : Lattice) :
    (ABB n).ρ (nIn phiBB m) = (planeRep n).ρ m := by
  have h := ABB_nIn n m
  rw [planeRep_rho]
  exact h

theorem he_BB (n : ℕ) (g : Lattice) (v : PolynomialGLAction.HomogeneousPoly n) :
    (radicalRep phiBB (ABB n)).ρ g v = (planeRep n).ρ g v :=
  LinearMap.congr_fun (radical_rho_BB1 n g) v

/-- The identification of the radical representation of the edge group with `planeRep n`. -/
def eqBB (n : ℕ) : radicalRep phiBB (ABB n) ≃ₗ[ℚ] planeRep n :=
  LinearEquiv.refl ℚ (PolynomialGLAction.HomogeneousPoly n)

theorem heBB (n : ℕ) (g : Lattice) (v : radicalRep phiBB (ABB n)) :
    (eqBB n) ((radicalRep phiBB (ABB n)).ρ g v) = (planeRep n).ρ g ((eqBB n) v) :=
  he_BB n g v

def thetaBB (n : ℕ) : groupCohomology (radicalRep phiBB (ABB n)) 1 ≃ₗ[ℚ] groupCohomology (planeRep n) 1 :=
  transportH1 (eqBB n) (heBB n)

end Theta

section Intertwine

open TernaryPoly.RadicalFirstCohomology TernaryPoly.RadicalTopCohomology

theorem phiBB_inv_apply (m : Lattice) :
    (phiBB (Multiplicative.ofAdd 1)⁻¹ m) = matrixLattice binaryUpper⁻¹ m := by
  apply Multiplicative.toAdd.injective
  rw [phiBB_apply, matrixLattice_coordinates]
  have hv : (binaryUpper⁻¹).val = ![![1, -1], ![0, 1]] := rfl
  rw [hv]
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem theta_Q_BB (n : ℕ) (x : groupCohomology (radicalRep phiBB (ABB n)) 1) :
    thetaBB n ((cohomologyRep phiBB (ABB n) 1).ρ (Multiplicative.ofAdd 1) x) =
      planeH1Action n binaryUpper (thetaBB n x) := by
  induction x using H1_induction_on with | h c => ?_
  rw [H1π_action, thetaBB, transportH1_H1π, transportH1_H1π, planeH1Action, H1π_comp_map_apply]
  have hcoc : transportC (eqBB n) (heBB n) (cocyclesOneAction phiBB (ABB n) (Multiplicative.ofAdd 1) c) =
      mapCocycles₁ (matrixLattice binaryUpper⁻¹).toMonoidHom (planeCoefficientHom n binaryUpper)
        (transportC (eqBB n) (heBB n) c) := by
    apply Subtype.ext
    funext m
    have h1 : (ABB n).ρ (qIn phiBB (Multiplicative.ofAdd 1)) =
        PolynomialGLAction.integralAction n 0 (planeElement binaryUpper 0) := by
      rw [ABB_qIn, TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables.planeElement_upper]
      rfl
    change (((ABB n).ρ (qIn phiBB (Multiplicative.ofAdd 1)) (c.1 (phiBB (Multiplicative.ofAdd 1)⁻¹ m)) :
        PolynomialGLAction.HomogeneousPoly n)) =
      PolynomialGLAction.integralAction n 0 (planeElement binaryUpper 0) (c.1 (matrixLattice binaryUpper⁻¹ m))
    rw [phiBB_inv_apply]
    exact LinearMap.congr_fun h1 _
  rw [hcoc]

theorem theta_twist_BB (n : ℕ) (ε : ℤˣ × ℤˣ) (x : groupCohomology (radicalRep phiBB (ABB n)) 1) :
    thetaBB n ((twistBB n ε).twistN x) = planeH1Action n (TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables.diagGL2 ε) (thetaBB n x) := by
  induction x using H1_induction_on with | h c => ?_
  rw [Twist.twistN, H1π_comp_map_apply, thetaBB, transportH1_H1π, transportH1_H1π, planeH1Action,
    H1π_comp_map_apply]
  have hcoc : transportC (eqBB n) (heBB n) (mapCocycles₁ (twistBB n ε).ψ (twistBB n ε).TN c) =
      mapCocycles₁ (matrixLattice (TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables.diagGL2 ε)⁻¹).toMonoidHom
        (planeCoefficientHom n (TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables.diagGL2 ε))
        (transportC (eqBB n) (heBB n) c) := by
    apply Subtype.ext
    funext m
    change (PolynomialGLAction.integralAction n 0 (diagonalHom ε) (c.1 (psiBB ε m)) :
        PolynomialGLAction.HomogeneousPoly n) =
      PolynomialGLAction.integralAction n 0
        (planeElement (TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables.diagGL2 ε) 0)
        (c.1 (matrixLattice (TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables.diagGL2 ε)⁻¹ m))
    rw [TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables.planeElement_diagGL2]
    rfl
  rw [hcoc]

end Intertwine

section Final

open MvPolynomial
open TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables (zPow weight)

theorem qIn_zPow (n : ℕ) :
    (ABB n).ρ (qIn phiBB (Multiplicative.ofAdd 1)) (zPow n) = zPow n := by
  have h : (ABB n).ρ (qIn phiBB (Multiplicative.ofAdd 1)) = PolynomialGLAction.integralAction n 0 (rootElement 0 1) := by
    rw [ABB_qIn]; rfl
  rw [h, integralAction_root]
  apply Subtype.ext
  change shear 0 1 (X 2 ^ n : Poly) = X 2 ^ n
  simp [shear]

theorem mem_inv_BB (n : ℕ) (v : radicalRep phiBB (ABB n)) :
    v ∈ (radicalRep phiBB (ABB n)).ρ.invariants ↔ ∀ g, (radicalRep phiBB (ABB n)).ρ g v = v :=
  Representation.mem_invariants _ _

theorem mem_inv_BB' (n : ℕ) (v : PolynomialGLAction.HomogeneousPoly n) :
    (∀ g, (radicalRep phiBB (ABB n)).ρ g v = v) ↔ ∀ g, (planeRep n).ρ g v = v :=
  forall_congr' fun g => by rw [he_BB n g v]; exact Iff.rfl

end Final

section MainBB

open MvPolynomial TernaryPoly.RadicalFirstCohomology
open TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables (zPow weight diagGL2 planeRadical_invariants zPow_diagonal bb_second_weight)

theorem sBB_eq_weight (ε : ℤˣ × ℤˣ) : ((sBB ε : ℤ) : ℚ) = weight (-1) 1 ε := by
  rcases Int.units_eq_one_or ε.1 with h1 | h1 <;> rcases Int.units_eq_one_or ε.2 with h2 | h2 <;>
    simp [sBB, weight, h1, h2]

theorem zPow_ne_zero (n : ℕ) : zPow n ≠ 0 := by
  intro h
  have := congrArg (fun p : PolynomialGLAction.HomogeneousPoly n => (p : Poly)) h
  exact pow_ne_zero _ (X_ne_zero (2 : Fin 3)) this

/-- **Edge type `BB`: the two subquotients of `H¹(N_edge, E)`.** For `N_edge = ⟨U₁₂, U₁₃, U₂₃⟩ ≅ N_P ⋊ ⟨E₁₂⟩` and
`E = Sym^n((ℚ³)*)`:
`0 → H¹(ℤ, E^{N_P}) → H¹(N_edge, E) → H¹(N_P, E)^ℤ → 0` is exact (`infl` injective, `ker resp = range infl`, and the image of
`resp` is the line of the `E₁₂`-invariants of `H¹(N_P, E)`, identified with `planeRep n` by `thetaBB`); `H¹(N_edge, E)` has the basis
`x₁, x₂` with `x₁` spanning the first subquotient, `D₀ = {diag(η₁, η₂, 1)}` acts on `x₁` by the weight `(-1, 1, -n)` and on
`x₂` modulo `x₁` by the weight `(0, -n-1, 1)`. -/
theorem bb_edge_subquotients (n : ℕ) :
    ∃ x₁ x₂ : groupCohomology (ABB n) 1,
      x₁ ≠ 0 ∧
      Function.Injective (infl phiBB (ABB n)).hom ∧
      LinearMap.range (infl phiBB (ABB n)).hom = Submodule.span ℚ {x₁} ∧
      LinearMap.ker (resp phiBB (ABB n)).hom = Submodule.span ℚ {x₁} ∧
      (∀ v : groupCohomology (planeRep n) 1, planeH1Action n binaryUpper v = v ↔
        ∃ y : groupCohomology (ABB n) 1, thetaBB n (resp phiBB (ABB n) y) = v) ∧
      thetaBB n (resp phiBB (ABB n) x₂) ≠ 0 ∧
      (∀ x : groupCohomology (ABB n) 1, ∃ a b : ℚ, x = a • x₁ + b • x₂) ∧
      (∀ a b : ℚ, a • x₁ + b • x₂ = 0 → a = 0 ∧ b = 0) ∧
      (∀ ε : ℤˣ × ℤˣ, (twistBB n ε).twistG x₁ = weight (-1) 1 ε • x₁) ∧
      (∀ ε : ℤˣ × ℤˣ, ∃ μ : ℚ, (twistBB n ε).twistG x₂ = weight 0 (-((n : ℤ) + 1)) ε • x₂ + μ • x₁) := by
  obtain ⟨v₀', hv₀', hinv', heig⟩ := bb_second_weight n
  let v₀ := (thetaBB n).symm v₀'
  have hv₀ : v₀ ≠ 0 := fun h => hv₀' (by simpa [v₀] using congrArg (thetaBB n) h)
  have hinv : ∀ x : groupCohomology (radicalRep phiBB (ABB n)) 1,
      (cohomologyRep phiBB (ABB n) 1).ρ (Multiplicative.ofAdd 1) x = x ↔ ∃ c : ℚ, x = c • v₀ := by
    intro x
    rw [← (thetaBB n).injective.eq_iff, theta_Q_BB, hinv' (thetaBB n x)]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, (thetaBB n).injective (by simpa [v₀] using hc)⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, by simp [v₀]⟩
  let w₀ : radicalRep phiBB (ABB n) := (zPow n : PolynomialGLAction.HomogeneousPoly n)
  have hzfix : ∀ g, (planeRep n).ρ g (zPow n) = zPow n := fun g =>
    (planeRadical_invariants n (zPow n)).mpr ⟨1, (one_smul _ _).symm⟩ g
  have hw₀ : w₀ ∈ (radicalRep phiBB (ABB n)).ρ.invariants :=
    (mem_inv_BB n w₀).mpr ((mem_inv_BB' n (zPow n)).mpr hzfix)
  have hspan : ∀ v ∈ (radicalRep phiBB (ABB n)).ρ.invariants, ∃ (c : ℚ) (u : ABB n),
      u ∈ (radicalRep phiBB (ABB n)).ρ.invariants ∧
        v = c • w₀ + ((ABB n).ρ (qIn phiBB (Multiplicative.ofAdd 1)) u - u) := by
    intro v hv
    obtain ⟨c, hc⟩ := (planeRadical_invariants n v).mp ((mem_inv_BB' n v).mp ((mem_inv_BB n v).mp hv))
    refine ⟨c, 0, Submodule.zero_mem _, ?_⟩
    rw [map_zero, sub_zero, add_zero]
    exact hc
  have hnz : ∀ u ∈ (radicalRep phiBB (ABB n)).ρ.invariants,
      (ABB n).ρ (qIn phiBB (Multiplicative.ofAdd 1)) u - u ≠ w₀ := by
    intro u hu
    obtain ⟨c, hc⟩ := (planeRadical_invariants n u).mp ((mem_inv_BB' n u).mp ((mem_inv_BB n u).mp hu))
    have hu' : u = c • w₀ := hc
    have h1 : (ABB n).ρ (qIn phiBB (Multiplicative.ofAdd 1)) u = u := by
      rw [hu', map_smul]
      exact congrArg (c • ·) (qIn_zPow n)
    rw [h1, sub_self]
    exact fun h => zPow_ne_zero n h.symm
  obtain ⟨c₁, x₂, hc₁N, hc₁t, hx₁, hinj, hrange, hker, hrr, hx₂, hspan', hind⟩ :=
    edge_basis w₀ hw₀ hspan hnz v₀ hv₀ hinv
  have hΘv₀ : thetaBB n v₀ = v₀' := (thetaBB n).apply_symm_apply v₀'
  refine ⟨H1π _ c₁, x₂, hx₁, hinj, hrange, hker, ?_, ?_, hspan', hind, ?_, ?_⟩
  · intro v
    constructor
    · intro hv
      obtain ⟨c, hc⟩ := (hinv' v).mp hv
      refine ⟨c • x₂, ?_⟩
      rw [map_smul, hx₂, map_smul, hΘv₀, hc]
    · rintro ⟨y, rfl⟩
      have hy : resp phiBB (ABB n) y ∈ LinearMap.range (resp phiBB (ABB n)).hom := ⟨y, rfl⟩
      rw [hrr, Submodule.mem_span_singleton] at hy
      obtain ⟨c, hc⟩ := hy
      refine (hinv' _).mpr ⟨c, ?_⟩
      rw [← hc, map_smul, hΘv₀]
  · rw [hx₂, hΘv₀]; exact hv₀'
  · intro ε
    have h := (twistBB n ε).twist_left w₀ hw₀ (zPow_diagonal n ε) c₁ hc₁N hc₁t
    rw [h]
    change ((sBB ε : ℤ) : ℚ) • _ = _
    rw [sBB_eq_weight]
  · intro ε
    refine (twistBB n ε).twist_right (H1π _ c₁) x₂ v₀ hker hx₂ (weight 0 (-((n : ℤ) + 1)) ε) ?_
    apply (thetaBB n).injective
    rw [theta_twist_BB, hΘv₀, heig ε, map_smul, hΘv₀]

end MainBB


open TernaryPoly.RelativeEdgeCohomologyMatrices

/-- Conjugation by the root `3E₃₂` on the line lattice `⟨U₁₂, U₁₃⟩`: `(a, b) ↦ (a - 3 q b, b)`. -/
def phiBG : Multiplicative ℤ →* MulAut Lattice where
  toFun q :=
    { toFun := fun g => Multiplicative.ofAdd (g.toAdd.1 - 3 * q.toAdd * g.toAdd.2, g.toAdd.2)
      invFun := fun g => Multiplicative.ofAdd (g.toAdd.1 + 3 * q.toAdd * g.toAdd.2, g.toAdd.2)
      left_inv := fun g => by
        apply Multiplicative.toAdd.injective
        simp
      right_inv := fun g => by
        apply Multiplicative.toAdd.injective
        simp
      map_mul' := fun g h => by
        apply Multiplicative.toAdd.injective
        simp only [toAdd_mul, toAdd_ofAdd, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
        congr 1
        ring }
  map_one' := by
    apply MulEquiv.ext
    intro g
    apply Multiplicative.toAdd.injective
    simp
  map_mul' q r := by
    apply MulEquiv.ext
    intro g
    apply Multiplicative.toAdd.injective
    simp only [MulAut.mul_apply, MulEquiv.coe_mk, Equiv.coe_fn_mk, toAdd_ofAdd, toAdd_mul]
    congr 1
    ring

theorem phiBG_apply (q : Multiplicative ℤ) (g : Lattice) :
    (phiBG q g).toAdd = (g.toAdd.1 - 3 * q.toAdd * g.toAdd.2, g.toAdd.2) := rfl

/-- The root group `⟨3E₃₂⟩` as a homomorphism from `ℤ`. -/
def rootBG : Multiplicative ℤ →* IntegralGL where
  toFun q := (bgRoot 1 q.toAdd).val
  map_one' := by simp
  map_mul' q r := by
    change (bgRoot 1 (q.toAdd + r.toAdd)).val = (bgRoot 1 q.toAdd).val * (bgRoot 1 r.toAdd).val
    rw [← bgRoot_mul]; rfl

theorem rootBG_mul_lineHom (q : Multiplicative ℤ) (g : Lattice) :
    rootBG q * lineHom g = lineHom (phiBG q g) * rootBG q := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have h := phiBG_apply q g
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [rootBG, bgRoot, bgElement_val, bgMatrix, lineHom, lineElement_val, lineMatrix,
      Fin.sum_univ_three, h]
  all_goals ring

theorem commBG (q : Multiplicative ℤ) :
    lineHom.comp (phiBG q).toMonoidHom = (MulAut.conj (rootBG q)).toMonoidHom.comp lineHom := by
  apply MonoidHom.ext
  intro g
  change lineHom (phiBG q g) = rootBG q * lineHom g * (rootBG q)⁻¹
  rw [rootBG_mul_lineHom, mul_inv_cancel_right]

/-- The edge group `N_L ⋊ ⟨3E₃₂⟩` as an abstract semidirect product. -/
abbrev GBG := Lattice ⋊[phiBG] Multiplicative ℤ

def eBG : GBG →* IntegralGL := SemidirectProduct.lift lineHom rootBG commBG

def ABG (n : ℕ) : Rep.{0} ℚ GBG := Rep.of ((PolynomialGLAction.integralAction n 0).comp eBG)

theorem ABG_nIn (n : ℕ) (m : Lattice) :
    (ABG n).ρ (nIn phiBG m) = PolynomialGLAction.integralAction n 0 (lineHom m) := by
  change PolynomialGLAction.integralAction n 0 (eBG (nIn phiBG m)) = _
  rw [show eBG (nIn phiBG m) = lineHom m from SemidirectProduct.lift_inl _ _ _ _]

theorem ABG_qIn (n : ℕ) (q : Multiplicative ℤ) :
    (ABG n).ρ (qIn phiBG q) = PolynomialGLAction.integralAction n 0 (bgRoot 1 q.toAdd).val := by
  change PolynomialGLAction.integralAction n 0 (eBG (qIn phiBG q)) = _
  rw [show eBG (qIn phiBG q) = rootBG q from SemidirectProduct.lift_inr _ _ _ _]
  rfl

section TwistBG

open TernaryPoly.SymmetricLineCohomology
open TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables (diagGL2')

/-- Inverse conjugation of the line lattice by `diag(η₁, diag(η₂, 1))`. -/
def psiBG (ε : ℤˣ × ℤˣ) : Lattice →* Lattice := leviLatticeChange ε.1 (diagGL2' ε.2)

theorem psiBG_apply (ε : ℤˣ × ℤˣ) (g : Lattice) :
    (psiBG ε g).toAdd = ((ε.1⁻¹).val * (g.toAdd.1 * ε.2.val), (ε.1⁻¹).val * g.toAdd.2) := by
  simp [psiBG, leviLatticeChange, diagGL2']

/-- The exponent by which conjugation by `diag(η₁, η₂, 1)⁻¹` scales the root `3E₃₂`: `η₂`. -/
def sBG (ε : ℤˣ × ℤˣ) : ℤ := ε.2.val

theorem sBG_cases (ε : ℤˣ × ℤˣ) : sBG ε = 1 ∨ sBG ε = -1 := by
  rcases Int.units_eq_one_or ε.2 with h | h <;> simp [sBG, h]

theorem psiBG_compat (ε : ℤˣ × ℤˣ) (q : Multiplicative ℤ) :
    (psiBG ε).comp (phiBG q).toMonoidHom =
      (phiBG (zpowGroupHom (sBG ε) q)).toMonoidHom.comp (psiBG ε) := by
  apply MonoidHom.ext
  intro g
  apply Multiplicative.toAdd.injective
  change (psiBG ε (phiBG q g)).toAdd = (phiBG (zpowGroupHom (sBG ε) q) (psiBG ε g)).toAdd
  rw [psiBG_apply, phiBG_apply, phiBG_apply, psiBG_apply]
  rcases Int.units_eq_one_or ε.1 with h1 | h1 <;> rcases Int.units_eq_one_or ε.2 with h2 | h2 <;>
    simp [sBG, h1, h2] <;> ring

end TwistBG

section TwistBG2

open TernaryPoly.SymmetricLineCohomology
open TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables (diagGL2')

theorem psiBG_surjective (ε : ℤˣ × ℤˣ) : Function.Surjective (psiBG ε) := by
  intro g
  refine ⟨Multiplicative.ofAdd (ε.1.val * ε.2.val * g.toAdd.1, ε.1.val * g.toAdd.2), ?_⟩
  apply Multiplicative.toAdd.injective
  rw [psiBG_apply]
  rcases Int.units_eq_one_or ε.1 with h1 | h1 <;> rcases Int.units_eq_one_or ε.2 with h2 | h2 <;>
    simp [h1, h2]

theorem diag_lineHom (ε : ℤˣ × ℤˣ) (m : Lattice) :
    diagonalHom ε * lineHom (psiBG ε m) = lineHom m * diagonalHom ε := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  have h := psiBG_apply ε m
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rcases Int.units_eq_one_or ε.1 with h1 | h1 <;> rcases Int.units_eq_one_or ε.2 with h2 | h2 <;>
    fin_cases i <;> fin_cases j <;>
    simp [diagonalHom, lineHom, lineElement_val, lineMatrix, bbElement_val, bbMatrix, Fin.sum_univ_three,
      h, h1, h2]

theorem diag_rootBG (ε : ℤˣ × ℤˣ) (q : Multiplicative ℤ) :
    diagonalHom ε * rootBG (zpowGroupHom (sBG ε) q) = rootBG q * diagonalHom ε := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rcases Int.units_eq_one_or ε.1 with h1 | h1 <;> rcases Int.units_eq_one_or ε.2 with h2 | h2 <;>
    fin_cases i <;> fin_cases j <;>
    simp [diagonalHom, rootBG, bgRoot, bgElement_val, bgMatrix, bbElement_val, bbMatrix, Fin.sum_univ_three,
      sBG, h1, h2]

end TwistBG2

section TwistBG3

/-- The automorphism of the edge group `BG`. -/
def sigmaBG (ε : ℤˣ × ℤˣ) : GBG →* GBG :=
  SemidirectProduct.map (psiBG ε) (zpowGroupHom (sBG ε)) (psiBG_compat ε)

theorem eBG_sigma (ε : ℤˣ × ℤˣ) (g : GBG) :
    diagonalHom ε * eBG (sigmaBG ε g) = eBG g * diagonalHom ε := by
  have hl : ∀ m : Lattice, diagonalHom ε * eBG (sigmaBG ε (nIn phiBG m)) = eBG (nIn phiBG m) * diagonalHom ε := by
    intro m
    unfold sigmaBG
    rw [SemidirectProduct.map_inl]
    change diagonalHom ε * eBG (nIn phiBG (psiBG ε m)) = eBG (nIn phiBG m) * _
    rw [show eBG (nIn phiBG (psiBG ε m)) = lineHom (psiBG ε m) from SemidirectProduct.lift_inl _ _ _ _,
      show eBG (nIn phiBG m) = lineHom m from SemidirectProduct.lift_inl _ _ _ _]
    exact diag_lineHom ε m
  have hr : ∀ q : Multiplicative ℤ, diagonalHom ε * eBG (sigmaBG ε (qIn phiBG q)) = eBG (qIn phiBG q) * diagonalHom ε := by
    intro q
    unfold sigmaBG
    rw [SemidirectProduct.map_inr]
    change diagonalHom ε * eBG (qIn phiBG (zpowGroupHom (sBG ε) q)) = eBG (qIn phiBG q) * _
    rw [show eBG (qIn phiBG (zpowGroupHom (sBG ε) q)) = rootBG (zpowGroupHom (sBG ε) q) from
        SemidirectProduct.lift_inr _ _ _ _,
      show eBG (qIn phiBG q) = rootBG q from SemidirectProduct.lift_inr _ _ _ _]
    exact diag_rootBG ε q
  have hg : g = nIn phiBG g.left * qIn phiBG g.right := (SemidirectProduct.inl_left_mul_inr_right g).symm
  rw [hg, map_mul, map_mul, map_mul]
  calc diagonalHom ε * (eBG (sigmaBG ε (nIn phiBG g.left)) * eBG (sigmaBG ε (qIn phiBG g.right)))
      = (diagonalHom ε * eBG (sigmaBG ε (nIn phiBG g.left))) * eBG (sigmaBG ε (qIn phiBG g.right)) := by
        rw [mul_assoc]
    _ = eBG (nIn phiBG g.left) * diagonalHom ε * eBG (sigmaBG ε (qIn phiBG g.right)) := by rw [hl]
    _ = eBG (nIn phiBG g.left) * (diagonalHom ε * eBG (sigmaBG ε (qIn phiBG g.right))) := by rw [mul_assoc]
    _ = _ := by rw [hr, mul_assoc]

attribute [irreducible] eBG

/-- The twist of the edge group `BG` by `diag(η₁, η₂, 1)`. -/
def twistBG (n : ℕ) (ε : ℤˣ × ℤˣ) : Twist phiBG (ABG n) where
  ψ := psiBG ε
  s := sBG ε
  hs := sBG_cases ε
  hψ := psiBG_surjective ε
  compat := psiBG_compat ε
  T := PolynomialGLAction.integralAction n 0 (diagonalHom ε)
  hT := fun g v => by
    have hmat : PolynomialGLAction.integralAction n 0 (diagonalHom ε) *
        PolynomialGLAction.integralAction n 0 (eBG (sigmaBG ε g)) =
        PolynomialGLAction.integralAction n 0 (eBG g) *
        PolynomialGLAction.integralAction n 0 (diagonalHom ε) := by
      rw [← map_mul, ← map_mul, eBG_sigma]
    exact LinearMap.congr_fun hmat v

end TwistBG3

section ThetaBG

open TernaryPoly.SymmetricLineCohomology TernaryPoly.RadicalFirstCohomology
open TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables
  (diagGL2' lineH1LeviAction0 leviCoefficientHom0 lineElement_diagGL2' lineElement_lower)

theorem radical_rho_BG0 (n : ℕ) (m : Lattice) :
    (radicalRep phiBG (ABG n)).ρ m = (ABG n).ρ (nIn phiBG m) := rfl

theorem lineRep_rho (n : ℕ) (m : Lattice) :
    (lineRep n).ρ m = PolynomialGLAction.integralAction n 0 (lineHom m) := rfl

theorem radical_rho_BG1 (n : ℕ) (m : Lattice) :
    (ABG n).ρ (nIn phiBG m) = (lineRep n).ρ m := by
  have h := ABG_nIn n m
  rw [lineRep_rho]
  exact h

theorem he_BG (n : ℕ) (g : Lattice) (v : PolynomialGLAction.HomogeneousPoly n) :
    (radicalRep phiBG (ABG n)).ρ g v = (lineRep n).ρ g v :=
  LinearMap.congr_fun (radical_rho_BG1 n g) v

/-- The identification of the radical representation of the edge group with `lineRep n`. -/
def eqBG (n : ℕ) : radicalRep phiBG (ABG n) ≃ₗ[ℚ] lineRep n :=
  LinearEquiv.refl ℚ (PolynomialGLAction.HomogeneousPoly n)

theorem heBG (n : ℕ) (g : Lattice) (v : radicalRep phiBG (ABG n)) :
    (eqBG n) ((radicalRep phiBG (ABG n)).ρ g v) = (lineRep n).ρ g ((eqBG n) v) :=
  he_BG n g v

def thetaBG (n : ℕ) : groupCohomology (radicalRep phiBG (ABG n)) 1 ≃ₗ[ℚ] groupCohomology (lineRep n) 1 :=
  transportH1 (eqBG n) (heBG n)

theorem phiBG_inv_apply (m : Lattice) :
    (phiBG (Multiplicative.ofAdd 1)⁻¹ m) = leviLatticeChange 1 (TernaryPoly.OrdinaryFaceRadical.binaryLowerStep 3) m := by
  apply Multiplicative.toAdd.injective
  rw [phiBG_apply]
  simp [leviLatticeChange, TernaryPoly.OrdinaryFaceRadical.binaryLowerStep,
    TernaryPoly.OrdinaryFaceRadical.binaryLowerMatrix, mul_comm]

theorem theta_Q_BG (n : ℕ) (x : groupCohomology (radicalRep phiBG (ABG n)) 1) :
    thetaBG n ((cohomologyRep phiBG (ABG n) 1).ρ (Multiplicative.ofAdd 1) x) =
      lineH1LeviAction0 n 1 (TernaryPoly.OrdinaryFaceRadical.binaryLowerStep 3) (thetaBG n x) := by
  induction x using H1_induction_on with | h c => ?_
  rw [H1π_action, thetaBG, transportH1_H1π, transportH1_H1π, lineH1LeviAction0, H1π_comp_map_apply]
  have hcoc : transportC (eqBG n) (heBG n) (cocyclesOneAction phiBG (ABG n) (Multiplicative.ofAdd 1) c) =
      mapCocycles₁ (leviLatticeChange 1 (TernaryPoly.OrdinaryFaceRadical.binaryLowerStep 3))
        (leviCoefficientHom0 n 1 (TernaryPoly.OrdinaryFaceRadical.binaryLowerStep 3))
        (transportC (eqBG n) (heBG n) c) := by
    apply Subtype.ext
    funext m
    have h1 : (ABG n).ρ (qIn phiBG (Multiplicative.ofAdd 1)) =
        PolynomialGLAction.integralAction n 0 (lineElement 1 0 (TernaryPoly.OrdinaryFaceRadical.binaryLowerStep 3)) := by
      rw [ABG_qIn, lineElement_lower]
      rfl
    change (((ABG n).ρ (qIn phiBG (Multiplicative.ofAdd 1)) (c.1 (phiBG (Multiplicative.ofAdd 1)⁻¹ m)) :
        PolynomialGLAction.HomogeneousPoly n)) =
      PolynomialGLAction.integralAction n 0
        (lineElement 1 0 (TernaryPoly.OrdinaryFaceRadical.binaryLowerStep 3))
        (c.1 (leviLatticeChange 1 (TernaryPoly.OrdinaryFaceRadical.binaryLowerStep 3) m))
    rw [phiBG_inv_apply]
    exact LinearMap.congr_fun h1 _
  rw [hcoc]

theorem theta_twist_BG (n : ℕ) (ε : ℤˣ × ℤˣ) (x : groupCohomology (radicalRep phiBG (ABG n)) 1) :
    thetaBG n ((twistBG n ε).twistN x) = lineH1LeviAction0 n ε.1 (diagGL2' ε.2) (thetaBG n x) := by
  induction x using H1_induction_on with | h c => ?_
  rw [Twist.twistN, H1π_comp_map_apply, thetaBG, transportH1_H1π, transportH1_H1π, lineH1LeviAction0,
    H1π_comp_map_apply]
  have hcoc : transportC (eqBG n) (heBG n) (mapCocycles₁ (twistBG n ε).ψ (twistBG n ε).TN c) =
      mapCocycles₁ (leviLatticeChange ε.1 (diagGL2' ε.2)) (leviCoefficientHom0 n ε.1 (diagGL2' ε.2))
        (transportC (eqBG n) (heBG n) c) := by
    apply Subtype.ext
    funext m
    change (PolynomialGLAction.integralAction n 0 (diagonalHom ε) (c.1 (psiBG ε m)) :
        PolynomialGLAction.HomogeneousPoly n) =
      PolynomialGLAction.integralAction n 0 (lineElement ε.1 0 (diagGL2' ε.2))
        (c.1 (leviLatticeChange ε.1 (diagGL2' ε.2) m))
    rw [lineElement_diagGL2']
    rfl
  rw [hcoc]

end ThetaBG

section MainBG

open MvPolynomial TernaryPoly.RadicalFirstCohomology TernaryPoly.SymmetricLineCohomology
open TernaryPeriodPolynomials.Argument.Statements.RadicalCohomologyTables
  (zPow weight diagGL2' lineH1LeviAction0 lineRadical_invariants zPow_diagonal bg_second_weight bg_first_weight)

theorem sBG_eq_weight (ε : ℤˣ × ℤˣ) : ((sBG ε : ℤ) : ℚ) = weight 0 1 ε := by
  rcases Int.units_eq_one_or ε.2 with h2 | h2 <;> simp [sBG, weight, h2]

theorem mem_inv_BG (n : ℕ) (v : radicalRep phiBG (ABG n)) :
    v ∈ (radicalRep phiBG (ABG n)).ρ.invariants ↔ ∀ g, (radicalRep phiBG (ABG n)).ρ g v = v :=
  Representation.mem_invariants _ _

theorem mem_inv_BG' (n : ℕ) (v : PolynomialGLAction.HomogeneousPoly n) :
    (∀ g, (radicalRep phiBG (ABG n)).ρ g v = v) ↔ ∀ g, (lineRep n).ρ g v = v :=
  forall_congr' fun g => by rw [he_BG n g v]; exact Iff.rfl

theorem qIn_BG (n : ℕ) (u : radicalRep phiBG (ABG n)) :
    (ABG n).ρ (qIn phiBG (Multiplicative.ofAdd 1)) u =
      (PolynomialGLAction.integralAction n 0 (bgRoot 1 1).val) u := by
  rw [ABG_qIn]; rfl

/-- **Edge type `BG`: the two subquotients of `H¹(N_edge, E)`.** For `N_edge = ⟨U₁₂, U₁₃, 3E₃₂⟩ ≅ N_L ⋊ ⟨3E₃₂⟩` and
`E = Sym^n((ℚ³)*)`: `0 → H¹(ℤ, E^{N_L}) → H¹(N_edge, E) → H¹(N_L, E)^ℤ → 0` is exact; `H¹(N_edge, E)` has the basis `x₁, x₂`
with `x₁` spanning the first subquotient, `D₀` acts on `x₁` by the weight `(0, 1, -n-1)` and on `x₂` modulo `x₁` by the weight
`(-1, -n, 1)`. -/
theorem bg_edge_subquotients (n : ℕ) :
    ∃ x₁ x₂ : groupCohomology (ABG n) 1,
      x₁ ≠ 0 ∧
      Function.Injective (infl phiBG (ABG n)).hom ∧
      LinearMap.range (infl phiBG (ABG n)).hom = Submodule.span ℚ {x₁} ∧
      LinearMap.ker (resp phiBG (ABG n)).hom = Submodule.span ℚ {x₁} ∧
      (∀ v : groupCohomology (lineRep n) 1,
        lineH1LeviAction0 n 1 (TernaryPoly.OrdinaryFaceRadical.binaryLowerStep 3) v = v ↔
          ∃ y : groupCohomology (ABG n) 1, thetaBG n (resp phiBG (ABG n) y) = v) ∧
      thetaBG n (resp phiBG (ABG n) x₂) ≠ 0 ∧
      (∀ x : groupCohomology (ABG n) 1, ∃ a b : ℚ, x = a • x₁ + b • x₂) ∧
      (∀ a b : ℚ, a • x₁ + b • x₂ = 0 → a = 0 ∧ b = 0) ∧
      (∀ ε : ℤˣ × ℤˣ, (twistBG n ε).twistG x₁ = weight 0 1 ε • x₁) ∧
      (∀ ε : ℤˣ × ℤˣ, ∃ μ : ℚ, (twistBG n ε).twistG x₂ = weight (-1) (-(n : ℤ)) ε • x₂ + μ • x₁) := by
  obtain ⟨v₀', hv₀', hinv', heig⟩ := bg_second_weight n
  let v₀ := (thetaBG n).symm v₀'
  have hv₀ : v₀ ≠ 0 := fun h => hv₀' (by simpa [v₀] using congrArg (thetaBG n) h)
  have hinv : ∀ x : groupCohomology (radicalRep phiBG (ABG n)) 1,
      (cohomologyRep phiBG (ABG n) 1).ρ (Multiplicative.ofAdd 1) x = x ↔ ∃ c : ℚ, x = c • v₀ := by
    intro x
    rw [← (thetaBG n).injective.eq_iff, theta_Q_BG, hinv' (thetaBG n x)]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, (thetaBG n).injective (by simpa [v₀] using hc)⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, by simp [v₀]⟩
  obtain ⟨hinvar, hspanBG, hnzBG, -, -⟩ := bg_first_weight n
  let w₀ : radicalRep phiBG (ABG n) := (zPow n : PolynomialGLAction.HomogeneousPoly n)
  have hzfree : erase 0 ((zPow n : PolynomialGLAction.HomogeneousPoly n) : Poly) = (zPow n : Poly) := by
    simp [zPow]
  have hzfix : ∀ g, (lineRep n).ρ g (zPow n) = zPow n := fun g => (hinvar (zPow n)).mpr hzfree g
  have hw₀ : w₀ ∈ (radicalRep phiBG (ABG n)).ρ.invariants :=
    (mem_inv_BG n w₀).mpr ((mem_inv_BG' n (zPow n)).mpr hzfix)
  have hspan : ∀ v ∈ (radicalRep phiBG (ABG n)).ρ.invariants, ∃ (c : ℚ) (u : ABG n),
      u ∈ (radicalRep phiBG (ABG n)).ρ.invariants ∧
        v = c • w₀ + ((ABG n).ρ (qIn phiBG (Multiplicative.ofAdd 1)) u - u) := by
    intro v hv
    have hvfree := (hinvar v).mp ((mem_inv_BG' n v).mp ((mem_inv_BG n v).mp hv))
    obtain ⟨c, u, hufree, hcu⟩ := hspanBG v hvfree
    refine ⟨c, u, (mem_inv_BG n u).mpr ((mem_inv_BG' n u).mpr ((hinvar u).mpr hufree)), ?_⟩
    have hq : ((ABG n).ρ (qIn phiBG (Multiplicative.ofAdd 1)) : PolynomialGLAction.HomogeneousPoly n →ₗ[ℚ]
        PolynomialGLAction.HomogeneousPoly n) u = (TernaryPoly.RelativeEdgeCohomologyActions.bgRep n).ρ (bgRoot 1 1) u :=
      qIn_BG n u
    have key : (c • (zPow n) + (((TernaryPoly.RelativeEdgeCohomologyActions.bgRep n).ρ (bgRoot 1 1) u) - u) :
        PolynomialGLAction.HomogeneousPoly n) = v := by
      apply Subtype.ext
      rw [hcu]
      simp [zPow]
    exact key.symm.trans (by rw [← hq]; rfl)
  have hnz : ∀ u ∈ (radicalRep phiBG (ABG n)).ρ.invariants,
      (ABG n).ρ (qIn phiBG (Multiplicative.ofAdd 1)) u - u ≠ w₀ := by
    intro u0 _ h
    let u : PolynomialGLAction.HomogeneousPoly n := u0
    have hq : ((ABG n).ρ (qIn phiBG (Multiplicative.ofAdd 1)) : PolynomialGLAction.HomogeneousPoly n →ₗ[ℚ]
        PolynomialGLAction.HomogeneousPoly n) u = (TernaryPoly.RelativeEdgeCohomologyActions.bgRep n).ρ (bgRoot 1 1) u :=
      qIn_BG n u0
    have h' : (TernaryPoly.RelativeEdgeCohomologyActions.bgRep n).ρ (bgRoot 1 1) u - u = zPow n := by
      rw [← hq]; exact h
    have := hnzBG 1 u (by rw [h']; simp [zPow])
    exact one_ne_zero this
  obtain ⟨c₁, x₂, hc₁N, hc₁t, hx₁, hinj, hrange, hker, hrr, hx₂, hspan', hind⟩ :=
    edge_basis w₀ hw₀ hspan hnz v₀ hv₀ hinv
  have hΘv₀ : thetaBG n v₀ = v₀' := (thetaBG n).apply_symm_apply v₀'
  refine ⟨H1π _ c₁, x₂, hx₁, hinj, hrange, hker, ?_, ?_, hspan', hind, ?_, ?_⟩
  · intro v
    constructor
    · intro hv
      obtain ⟨c, hc⟩ := (hinv' v).mp hv
      refine ⟨c • x₂, ?_⟩
      rw [map_smul, hx₂, map_smul, hΘv₀, hc]
    · rintro ⟨y, rfl⟩
      have hy : resp phiBG (ABG n) y ∈ LinearMap.range (resp phiBG (ABG n)).hom := ⟨y, rfl⟩
      rw [hrr, Submodule.mem_span_singleton] at hy
      obtain ⟨c, hc⟩ := hy
      refine (hinv' _).mpr ⟨c, ?_⟩
      rw [← hc, map_smul, hΘv₀]
  · rw [hx₂, hΘv₀]; exact hv₀'
  · intro ε
    have h := (twistBG n ε).twist_left w₀ hw₀ (zPow_diagonal n ε) c₁ hc₁N hc₁t
    rw [h]
    change ((sBG ε : ℤ) : ℚ) • _ = _
    rw [sBG_eq_weight]
  · intro ε
    refine (twistBG n ε).twist_right (H1π _ c₁) x₂ v₀ hker hx₂ (weight (-1) (-(n : ℤ)) ε) ?_
    apply (thetaBG n).injective
    rw [theta_twist_BG, hΘv₀, heig ε, map_smul, hΘv₀]

end MainBG

end TernaryPeriodPolynomials.Argument.Statements.EdgeSubquotients
