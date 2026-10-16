module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryResolution.Orbit

@[expose] public section

noncomputable section
namespace TernaryPoly.BoundaryFaceResolutionComparison
open CategoryTheory Category Limits Finsupp SingularComponentAugmentation

variable (G : Type) [Group G] {I : Type} (A : I → Type) [∀ i, MulAction G (A i)]

abbrev sigmaLabels := Rep.ofMulAction ℚ G (Σ i, A i)

def sigmaLabelInclusion (i : I) : Rep.ofMulAction ℚ G (A i) ⟶ sigmaLabels G A :=
  permutationMap (Sigma.mk i) (fun _ _ => rfl)

def sigmaLabelDescLinear {W : Rep.{0} ℚ G} (f : ∀ i, Rep.ofMulAction ℚ G (A i) ⟶ W) :
    sigmaLabels G A →ₗ[ℚ] W :=
  (Finsupp.lsum ℚ (fun x => (f x.1).hom.toLinearMap.comp (MonoidAlgebra.lsingle x.2))).comp
    (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

@[simp] theorem sigmaLabelDescLinear_single {W : Rep.{0} ℚ G}
    (f : ∀ i, Rep.ofMulAction ℚ G (A i) ⟶ W) (x : Σ i,A i) (r : ℚ) :
    sigmaLabelDescLinear G A f (MonoidAlgebra.single x r)=f x.1 (MonoidAlgebra.single x.2 r) := by
  change (Finsupp.lsum ℚ (fun y : Σ i,A i => (f y.1).hom.toLinearMap.comp (MonoidAlgebra.lsingle y.2)))
    (Finsupp.single x r)=_
  rw [Finsupp.lsum_single]
  rfl

def sigmaLabelDesc {W : Rep.{0} ℚ G} (f : ∀ i, Rep.ofMulAction ℚ G (A i) ⟶ W) :
    sigmaLabels G A ⟶ W :=
  Rep.ofHom ⟨sigmaLabelDescLinear G A f,fun g => by
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext
    intro r
    change sigmaLabelDescLinear G A f (Representation.ofMulAction ℚ G (Σ i,A i) g (MonoidAlgebra.single x r))=
      W.ρ g (sigmaLabelDescLinear G A f (MonoidAlgebra.single x r))
    rw [Representation.ofMulAction_single,sigmaLabelDescLinear_single,sigmaLabelDescLinear_single]
    change (f x.1).hom (MonoidAlgebra.single (g • x.2) r)=W.ρ g ((f x.1).hom (MonoidAlgebra.single x.2 r))
    simpa only [Representation.ofMulAction_single] using
      (Rep.hom_comm_apply (f x.1) g (MonoidAlgebra.single x.2 r))⟩

@[simp] theorem sigmaLabelDesc_single {W : Rep.{0} ℚ G}
    (f : ∀ i, Rep.ofMulAction ℚ G (A i) ⟶ W) (x : Σ i,A i) (r : ℚ) :
    sigmaLabelDesc G A f (MonoidAlgebra.single x r)=f x.1 (MonoidAlgebra.single x.2 r) :=
  sigmaLabelDescLinear_single G A f x r

/-- Linearization preserves the full disjoint union of actual orbit families. -/
def sigmaLabelsIso : (∐ fun i => Rep.ofMulAction ℚ G (A i)) ≅ sigmaLabels G A where
  hom := Sigma.desc (sigmaLabelInclusion G A)
  inv := sigmaLabelDesc G A (Sigma.ι _)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    rw [←Category.assoc,Sigma.ι_comp_desc,comp_id]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext
    intro r
    change sigmaLabelDesc G A (Sigma.ι _) (sigmaLabelInclusion G A i (MonoidAlgebra.single x r))=_
    rw [show sigmaLabelInclusion G A i (MonoidAlgebra.single x r)=MonoidAlgebra.single ⟨i,x⟩ r from
      permutationMap_single _ _ _ _,sigmaLabelDesc_single]
    rfl
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext
    intro r
    change (Sigma.desc (sigmaLabelInclusion G A)) (sigmaLabelDesc G A (Sigma.ι _) (MonoidAlgebra.single x r))=_
    rw [sigmaLabelDesc_single]
    have h := congrArg (fun m : Rep.ofMulAction ℚ G (A x.1) ⟶ sigmaLabels G A => m (MonoidAlgebra.single x.2 r))
      (Sigma.ι_comp_desc (sigmaLabelInclusion G A) x.1)
    exact h.trans (permutationMap_single _ _ _ _)

variable (X : Type) [MulAction G X]

abbrev labelOrbits := MulAction.orbitRel.Quotient G X
abbrev labelOrbit (o : labelOrbits G X) := MulAction.orbit G o.out

/-- The orbit partition equivalence retains every actual label. -/
def orbitPartition : (Σ o : labelOrbits G X,labelOrbit G X o) ≃ X :=
  (MulAction.selfEquivSigmaOrbits G X).symm

@[simp] theorem orbitPartition_apply (x : Σ o : labelOrbits G X,labelOrbit G X o) :
    orbitPartition G X x=x.2.val := rfl

theorem orbitPartition_equivariant (g : G) (x : Σ o : labelOrbits G X,labelOrbit G X o) :
    orbitPartition G X (g • x)=g • orbitPartition G X x := rfl

/-- Equivariant equivalences act on literal permutation coefficients. -/
def permutationIso {U V : Type} [MulAction G U] [MulAction G V]
    (e : U ≃ V) (he : ∀ (g : G) x,e (g • x)=g • e x) :
    Rep.ofMulAction ℚ G U ≅ Rep.ofMulAction ℚ G V where
  hom := permutationMap e he
  inv := permutationMap e.symm (fun g x => e.injective (by simp [he]))
  hom_inv_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext
    intro r
    change permutationMap e.symm (fun g x => e.injective (by simp [he]))
      (permutationMap e he (MonoidAlgebra.single x r))=MonoidAlgebra.single x r
    rw [permutationMap_single,permutationMap_single,e.symm_apply_apply]
  inv_hom_id := by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply MonoidAlgebra.lhom_ext'
    intro x
    apply LinearMap.ext
    intro r
    change permutationMap e he (permutationMap e.symm (fun g x => e.injective (by simp [he]))
      (MonoidAlgebra.single x r))=MonoidAlgebra.single x r
    rw [permutationMap_single,permutationMap_single,e.apply_symm_apply]

/-- The full label permutation module is exactly the coproduct of all actual orbit modules. -/
def orbitFamilyIso : (∐ fun o : labelOrbits G X => orbitLabels G o.out) ≅ Rep.ofMulAction ℚ G X := by
  change (∐ fun o : labelOrbits G X => Rep.ofMulAction ℚ G (labelOrbit G X o)) ≅ Rep.ofMulAction ℚ G X
  exact sigmaLabelsIso G (fun o : labelOrbits G X => ↥(labelOrbit G X o)) ≪≫ permutationIso G (orbitPartition G X) (orbitPartition_equivariant G X)

end TernaryPoly.BoundaryFaceResolutionComparison
