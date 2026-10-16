module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.SingularCap

@[expose] public section


/-!
# The cap of an equivariant singular cocycle intertwines the boundary maps

For a cocycle `f : C_a(E) ⟶ V` the cap `capE f : C_{a+b}(E) ⟶ V ⊗ C_b(E)` satisfies
`∂ ≫ capE f = (-1)^a • capE f ≫ (V ◁ ∂)` (the Leibniz rule for the Alexander-Whitney cap), from the library's
`aw_signed_identity`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory MonoidalCategory
open TernaryPoly TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularLocalHomology
open TernaryPoly.FreeActionLinearization
open TernaryPeriodPolynomials.Argument.TopHomology
open SphereOddDegree.AlexanderWhitney

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {G : Type} [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]

theorem capE_intertwine (V : Rep ℚ G) (a b : ℕ) (f : chainRep G E a ⟶ V)
    (hf : equivariantD G E (a+1) a ≫ f = 0) :
    equivariantD G E (a+b+1) (a+b) ≫ capE E V a b f =
      ((-1 : ℤ)^a) • (capE E V a (b+1) f ≫ (V ◁ equivariantD G E (b+1) b)) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply chainRep_linear_ext E
  intro σ
  have hL : (Rep.Hom.hom (equivariantD G E (a + b + 1) (a + b) ≫ capE E V a b f)).toLinearMap
      (chainElement G E (a + b + 1) σ) =
      ∑ k : Fin (a+b+2), (-1 : ℤ)^k.val • capElem E V a b f ((TopCat.toSSet.obj E).δ k σ) := by
    change (capE E V a b f).hom ((equivariantD G E (a + b + 1) (a + b)).hom (chainElement G E (a + b + 1) σ)) = _
    rw [chainElement_d]
    simp only [map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [capE_chainElement]
  have hR : (Rep.Hom.hom (((-1 : ℤ)^a) • (capE E V a (b+1) f ≫ (V ◁ equivariantD G E (b+1) b)))).toLinearMap
      (chainElement G E (a + b + 1) σ) =
      ((-1 : ℤ)^a) • ((V ◁ equivariantD G E (b+1) b).hom (capElem E V a (b+1) f σ)) := by
    rw [← capE_chainElement E V a (b+1) f σ]
    simp only [Rep.zsmul_hom, Rep.hom_comp]
    rfl
  rw [hL, hR]
  let F : SingularSimplex E a → V := fun τ => f.hom (chainElement G E a τ)
  let T : SingularSimplex E b → V →ₗ[ℚ] (V ⊗ chainRep G E b : Rep ℚ G) :=
    fun τ => (TensorProduct.mk ℚ V (chainRep G E b)).flip (chainElement G E b τ)
  have key := TernaryPoly.SingularLocalCap.aw_signed_identity (X := E) (W := V)
    (M := (V ⊗ chainRep G E b : Rep ℚ G)) a b F T σ
  set τ' := frontSimplex E (a+1) b (SphereOddDegree.awCastSimplex E a b σ) with hτ'
  have hz : ∑ i : Fin (a+2), (-1 : ℤ)^(i : ℕ) • F (faceSimplex E a i τ') = 0 := by
    have h0 := congrArg (fun φ : chainRep G E (a+1) ⟶ V => φ.hom (chainElement G E (a+1) τ')) hf
    change f.hom ((equivariantD G E (a+1) a).hom (chainElement G E (a+1) τ')) = 0 at h0
    rw [chainElement_d] at h0
    simp only [map_sum, map_zsmul] at h0
    exact h0
  rw [hz, map_zero, zero_add] at key
  refine Eq.trans key ?_
  congr 1
  change _ = (V ◁ equivariantD G E (b+1) b).hom (F (frontSimplex E a (b+1) σ) ⊗ₜ[ℚ] chainElement G E (b+1) (backSimplex E a (b+1) σ))
  rw [Rep.hom_whiskerLeft, Representation.IntertwiningMap.lTensor_apply]
  change _ = F (frontSimplex E a (b+1) σ) ⊗ₜ[ℚ] (equivariantD G E (b+1) b).hom (chainElement G E (b+1) (backSimplex E a (b+1) σ))
  rw [chainElement_d]
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul]
  rfl

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
