module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.GoodFlags
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalInner

@[expose] public section


/-!
# Shapiro surjectivity for the homogeneous `H²` of a permutation module

For a level group `L` (any subgroup of `GL₃(ℚ)`) acting on a set `X` and a representation `ρ`, the coordinates
`fixedPointH2 L ρ x : H²(L, Map(X, V)) → H²(L ∩ Stab x, V)` are jointly injective (`eq_zero_iff_fixedPointH2`, Sol).  Here we prove that
they are jointly *surjective on orbit representatives*: for any family of classes `z x ∈ H²(L ∩ Stab x, V)`, there is a class of
`H²(L, Map(X, V))` whose coordinate at every orbit representative `x` (`orbitRepresentative L x = x`) is `z x`
(`exists_fixedPointH2_eq`).  The proof is the degree-two version of `reconstructPrimitive`: the cochain
`C(v)(x) = ρ(t_x) c_{rep x}(t_x⁻¹ v)`.  We also record the naturality of `stabilizerTransportH2` with the restriction to a smaller
stabilizer and the resulting transport of `locallyInnerClasses`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.KDaggerComparison

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

variable {V : Type} [AddCommGroup V] [Module ℂ V] {X : Type} [MulAction RationalGL3 X]

/-- The homogeneous cochain of `L` with values in `Map(X, V)` built from a family of cochains of the stabilizers
`L ∩ Stab x`, determined by their values at the orbit representatives. -/
def reconstructCochain (L : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V) (d : ℕ)
    (c : ∀ x : X, cochains (fixedPointLevel L x) ρ d) : cochains L (functionRepresentation ρ X) d :=
  ⟨fun vertices point =>
    ρ (orbitTransport L point).val
      ((c (orbitRepresentative L point)).val
        (fun index => (orbitTransport L point).val⁻¹ * vertices index)), by
    intro element vertices
    funext point
    let previous := element.val⁻¹ • point
    let currentTransport := orbitTransport L point
    let previousTransport := orbitTransport L previous
    have sameRepresentative : orbitRepresentative L previous = orbitRepresentative L point :=
      orbitRepresentative_smul L element⁻¹ point
    let correction := currentTransport⁻¹ * element * previousTransport
    have fixes : correction.val • orbitRepresentative L point = orbitRepresentative L point := by
      change (currentTransport.val⁻¹ * element.val * previousTransport.val) •
        orbitRepresentative L point = orbitRepresentative L point
      rw [mul_smul, mul_smul, ← sameRepresentative]
      rw [orbitTransport_spec]
      change currentTransport.val⁻¹ • (element.val • (element.val⁻¹ • point)) = _
      rw [smul_inv_smul]
      rw [sameRepresentative]
      have transported := congrArg (fun flag => currentTransport.val⁻¹ • flag)
        (orbitTransport_spec L point)
      change currentTransport.val⁻¹ • (currentTransport.val •
        orbitRepresentative L point) = currentTransport.val⁻¹ • point at transported
      simpa only [inv_smul_smul] using transported.symm
    have correctionLevel : correction.val ∈ fixedPointLevel L (orbitRepresentative L point) :=
      ⟨correction.property, MulAction.mem_stabilizer_iff.mpr fixes⟩
    have equivariance := (c (orbitRepresentative L point)).property
      ⟨correction.val, correctionLevel⟩
      (fun index => previousTransport.val⁻¹ * vertices index)
    have vertexEquality :
        (fun index => currentTransport.val⁻¹ * (element.val * vertices index)) =
        (fun index => correction.val * (previousTransport.val⁻¹ * vertices index)) := by
      funext index
      change currentTransport.val⁻¹ * (element.val * vertices index) =
        (currentTransport.val⁻¹ * element.val * previousTransport.val) *
          (previousTransport.val⁻¹ * vertices index)
      group
    change ρ currentTransport.val
        ((c (orbitRepresentative L point)).val
          (fun index => currentTransport.val⁻¹ * (element.val * vertices index))) =
      ρ element.val
        (ρ previousTransport.val
          ((c (orbitRepresentative L previous)).val
            (fun index => previousTransport.val⁻¹ * vertices index)))
    rw [sameRepresentative, vertexEquality, equivariance]
    rw [← Module.End.mul_apply, ← map_mul]
    rw [← Module.End.mul_apply, ← map_mul]
    have productEquality : currentTransport.val * correction.val =
        element.val * previousTransport.val := by
      change currentTransport.val *
        (currentTransport.val⁻¹ * element.val * previousTransport.val) =
        element.val * previousTransport.val
      group
    rw [productEquality]⟩

theorem reconstructCochain_apply (L : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V) (d : ℕ)
    (c : ∀ x : X, cochains (fixedPointLevel L x) ρ d) (vertices : Fin (d + 1) → RationalGL3) (point : X) :
    (reconstructCochain L ρ d c).val vertices point =
      ρ (orbitTransport L point).val
        ((c (orbitRepresentative L point)).val
          (fun index => (orbitTransport L point).val⁻¹ * vertices index)) := rfl

/-- The reconstructed cochain of a family of cocycles is a cocycle. -/
theorem reconstructCochain_cocycle (L : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    (c : ∀ x : X, cocycles (fixedPointLevel L x) ρ) :
    differentialTwo L (functionRepresentation ρ X)
      (reconstructCochain L ρ 2 (fun x => (c x).val)) = 0 := by
  funext vertices point
  have vanishing := congrFun (c (orbitRepresentative L point)).property
    (fun index => (orbitTransport L point).val⁻¹ * vertices index)
  have translatedTriple (first second third : RationalGL3) :
      (fun index : Fin 3 => (orbitTransport L point).val⁻¹ * ![first, second, third] index) =
        ![(orbitTransport L point).val⁻¹ * first, (orbitTransport L point).val⁻¹ * second,
          (orbitTransport L point).val⁻¹ * third] := by
    funext index
    fin_cases index <;> rfl
  change ρ (orbitTransport L point).val
      ((c (orbitRepresentative L point)).val.val (fun index => (orbitTransport L point).val⁻¹ *
        ![vertices 1, vertices 2, vertices 3] index)) -
    ρ (orbitTransport L point).val
      ((c (orbitRepresentative L point)).val.val (fun index => (orbitTransport L point).val⁻¹ *
        ![vertices 0, vertices 2, vertices 3] index)) +
    ρ (orbitTransport L point).val
      ((c (orbitRepresentative L point)).val.val (fun index => (orbitTransport L point).val⁻¹ *
        ![vertices 0, vertices 1, vertices 3] index)) -
    ρ (orbitTransport L point).val
      ((c (orbitRepresentative L point)).val.val (fun index => (orbitTransport L point).val⁻¹ *
        ![vertices 0, vertices 1, vertices 2] index)) = 0
  simp only [translatedTriple]
  rw [← map_sub, ← map_add, ← map_sub]
  change ρ (orbitTransport L point).val
    ((c (orbitRepresentative L point)).val.val ![(orbitTransport L point).val⁻¹ * vertices 1,
        (orbitTransport L point).val⁻¹ * vertices 2, (orbitTransport L point).val⁻¹ * vertices 3] -
      (c (orbitRepresentative L point)).val.val ![(orbitTransport L point).val⁻¹ * vertices 0,
        (orbitTransport L point).val⁻¹ * vertices 2, (orbitTransport L point).val⁻¹ * vertices 3] +
      (c (orbitRepresentative L point)).val.val ![(orbitTransport L point).val⁻¹ * vertices 0,
        (orbitTransport L point).val⁻¹ * vertices 1, (orbitTransport L point).val⁻¹ * vertices 3] -
      (c (orbitRepresentative L point)).val.val ![(orbitTransport L point).val⁻¹ * vertices 0,
        (orbitTransport L point).val⁻¹ * vertices 1, (orbitTransport L point).val⁻¹ * vertices 2]) = 0
  have h0 : (c (orbitRepresentative L point)).val.val ![(orbitTransport L point).val⁻¹ * vertices 1,
        (orbitTransport L point).val⁻¹ * vertices 2, (orbitTransport L point).val⁻¹ * vertices 3] -
      (c (orbitRepresentative L point)).val.val ![(orbitTransport L point).val⁻¹ * vertices 0,
        (orbitTransport L point).val⁻¹ * vertices 2, (orbitTransport L point).val⁻¹ * vertices 3] +
      (c (orbitRepresentative L point)).val.val ![(orbitTransport L point).val⁻¹ * vertices 0,
        (orbitTransport L point).val⁻¹ * vertices 1, (orbitTransport L point).val⁻¹ * vertices 3] -
      (c (orbitRepresentative L point)).val.val ![(orbitTransport L point).val⁻¹ * vertices 0,
        (orbitTransport L point).val⁻¹ * vertices 1, (orbitTransport L point).val⁻¹ * vertices 2] = 0 :=
    vanishing
  rw [h0, map_zero]

/-- **Shapiro surjectivity (degree two).**  For every family of classes `z x ∈ H²(L ∩ Stab x, V)` there is a class of
`H²(L, Map(X, V))` whose coordinate at every orbit representative `x` is `z x`. -/
theorem exists_fixedPointH2_eq (L : Subgroup RationalGL3) (ρ : Representation ℂ RationalGL3 V)
    (z : ∀ x : X, H2 (fixedPointLevel L x) ρ) :
    ∃ y : H2 L (functionRepresentation ρ X),
      ∀ x : X, orbitRepresentative L x = x → fixedPointH2 L ρ x y = z x := by
  choose c hc using fun x : X => Submodule.Quotient.mk_surjective _ (z x)
  refine ⟨classOf L (functionRepresentation ρ X)
    ⟨reconstructCochain L ρ 2 (fun x => (c x).val), reconstructCochain_cocycle L ρ c⟩, ?_⟩
  intro x hx
  rw [← hc x]
  change classOf (fixedPointLevel L x) ρ _ = classOf (fixedPointLevel L x) ρ (c x)
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  funext vertices
  change ρ (orbitTransport L x).val
      ((c (orbitRepresentative L x)).val.val
        (fun index => (orbitTransport L x).val⁻¹ * vertices index)) = (c x).val.val vertices
  have hspec := orbitTransport_spec L x
  rw [hx] at hspec
  have hmem : (orbitTransport L x).val ∈ fixedPointLevel L x :=
    ⟨(orbitTransport L x).property, MulAction.mem_stabilizer_iff.mpr hspec⟩
  have hmem' : (orbitTransport L x).val⁻¹ ∈ fixedPointLevel L x := (fixedPointLevel L x).inv_mem hmem
  have e := (c x).val.property ⟨(orbitTransport L x).val⁻¹, hmem'⟩ vertices
  change (c x).val.val (fun index => (orbitTransport L x).val⁻¹ * vertices index) =
    ρ (orbitTransport L x).val⁻¹ ((c x).val.val vertices) at e
  rw [hx, e, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

end TernaryPeriodPolynomials.Argument.KDaggerComparison
