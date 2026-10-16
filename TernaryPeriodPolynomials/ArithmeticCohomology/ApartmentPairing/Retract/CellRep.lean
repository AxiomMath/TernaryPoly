module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Retract.CellChains
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology
public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Generators

@[expose] public section



/-!
# The cellular chain map at the level of `Γ(6)`-representations

`cellPermComplex : ChainComplex (Rep ℚ principalSix) ℕ` has the permutation representation on the cells of
grade `n` in degree `n` (`Γ(6)` acting through `levelOfSix : Γ(6) → Γ(3)`; it vanishes above degree three) and
the ℚ-form of the library's boundary (`dGr`, `cellD`, with `d² = 0` from `LQ_LQ`).  `cellChainMap` is the
morphism of complexes of `Γ(6)`-representations into the equivariant singular chains of `Glued`,
`C ↦ cellAt n C` (equivariance `cellAt_smul_six`, chain map property `d_cellAt`).  With coefficients `W`
(`cellCoinv W`), `cellCoinvMap_mk` gives the elementary chains, `cellToBordified W` lands in the geometric
local-coefficient chains `bordifiedLocalChains W` and `cellGroupHomologyMap W n` is the induced map from
the homology of the cellular complex with coefficients to the group homology `H_n(Γ(6), W)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical Pointwise

namespace TernaryPeriodPolynomials.Argument.Lemma33.Retract

open CategoryTheory Finsupp GeneralEisenstein TernaryPoly TernaryPoly.EquivariantSingularResolution
  TernaryPoly.SymmetricSpaceRationalGluing TernaryPoly.IntegralGL3Congruence
  TernaryPoly.SingularLocalHomology TernaryPoly.SymmetricSpaceBordifiedPrincipalSix
  TernaryPeriodPolynomials.FreeResolution
  TernaryPeriodPolynomials.TopVanishing

theorem levelLift_injective : Function.Injective levelLift := by
  intro a b h
  apply Subtype.ext
  rw [← integralToRational_levelLift a, ← integralToRational_levelLift b, h]

/-- `Γ(6) → Γ(3)` as a group homomorphism. -/
def levelOfSixHom : principalSix →* principalLevel where
  toFun := levelOfSix
  map_one' := by
    apply levelLift_injective
    rw [levelLift_levelOfSix, map_one]
    rfl
  map_mul' g h := by
    apply levelLift_injective
    rw [levelLift_levelOfSix, map_mul, levelLift_levelOfSix, levelLift_levelOfSix]
    rfl

instance : MulAction principalSix Cell := MulAction.compHom Cell levelOfSixHom

theorem six_smul_cell (g : principalSix) (C : Cell) : g • C = levelOfSix g • C := rfl

/-- Cells of a given grade. -/
abbrev Graded (n : ℕ) := {C : Cell // C.grade = n}

instance (n : ℕ) : MulAction principalSix (Graded n) where
  smul g C := ⟨g • C.1, by rw [six_smul_cell, Cell.grade_smul]; exact C.2⟩
  one_smul C := Subtype.ext (one_smul principalSix C.1)
  mul_smul g h C := Subtype.ext (mul_smul g h C.1)

theorem graded_smul_val (n : ℕ) (g : principalSix) (C : Graded n) : (g • C).1 = g • C.1 := rfl

/-- The boundary of a cell of grade `n + 1` as a chain of cells of grade `n`. -/
def dGr (n : ℕ) (C : Graded (n + 1)) : Graded n →₀ ℚ :=
  Finsupp.comapDomain Subtype.val (incQ C.1) Subtype.val_injective.injOn

theorem dGr_apply (n : ℕ) (C : Graded (n + 1)) (D : Graded n) : dGr n C D = incQ C.1 D.1 := rfl

theorem dGr_smul (n : ℕ) (g : principalSix) (C : Graded (n + 1)) :
    dGr n (g • C) = Finsupp.mapDomain (g • ·) (dGr n C) := by
  ext D
  obtain ⟨D', rfl⟩ : ∃ D' : Graded n, D = g • D' := ⟨g⁻¹ • D, by simp⟩
  rw [Finsupp.mapDomain_apply_of_injective (MulAction.injective g), dGr_apply, dGr_apply, graded_smul_val,
    graded_smul_val, six_smul_cell, six_smul_cell, incQ_smul,
    Finsupp.mapDomain_apply_of_injective (MulAction.injective (levelOfSix g))]

/-- The boundary as a linear map. -/
def dLin (n : ℕ) : (Graded (n + 1) →₀ ℚ) →ₗ[ℚ] (Graded n →₀ ℚ) := linearCombination ℚ (dGr n)

/-- The permutation representation on the cells of grade `n`. -/
abbrev cellRep (n : ℕ) : Rep ℚ principalSix := Rep.ofMulAction ℚ principalSix (Graded n)

/-- A `G`-equivariant linear map between permutation representations, given on finitely supported
functions. -/
def permHom {G : Type} [Group G] {S T : Type} [MulAction G S] [MulAction G T]
    (L : (S →₀ ℚ) →ₗ[ℚ] (T →₀ ℚ))
    (hL : ∀ (g : G) (C : S), L (single (g • C) 1) = Finsupp.mapDomain (g • ·) (L (single C 1))) :
    Rep.ofMulAction ℚ G S ⟶ Rep.ofMulAction ℚ G T :=
  Rep.ofHom ⟨(MonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap ∘ₗ L ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap, fun g => by
    have key : L ∘ₗ Finsupp.lmapDomain ℚ ℚ (g • ·) = Finsupp.lmapDomain ℚ ℚ (g • ·) ∘ₗ L := by
      apply Finsupp.lhom_ext
      intro C a
      have e : (single C a : S →₀ ℚ) = a • single C 1 := by simp
      rw [e]
      simp only [LinearMap.comp_apply, map_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rw [hL]
    apply LinearMap.ext
    intro z
    simp only [Representation.ofMulAction_def, LinearMap.comp_apply]
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact congrArg _ (LinearMap.congr_fun key _)⟩

/-- The boundary of the cellular permutation complex. -/
def cellD (n : ℕ) : cellRep (n + 1) ⟶ cellRep n :=
  permHom (dLin n) (fun g C => by
    simp only [dLin, linearCombination_single, one_smul]
    exact dGr_smul n g C)

/-- Grade-`n` cells as cells. -/
def incl (n : ℕ) : (Graded n →₀ ℚ) →ₗ[ℚ] (Cell →₀ ℚ) := Finsupp.lmapDomain ℚ ℚ Subtype.val

theorem incl_injective (n : ℕ) : Function.Injective (incl n) := by
  intro a b h
  exact Finsupp.mapDomain_injective Subtype.val_injective h

theorem incl_dGr (n : ℕ) (C : Graded (n + 1)) : incl n (dGr n C) = incQ C.1 := by
  rw [incl, Finsupp.lmapDomain_apply, dGr]
  refine Finsupp.mapDomain_comapDomain Subtype.val Subtype.val_injective _ ?_
  intro D hD
  have := incQ_grade C.1 D (Finsupp.mem_support_iff.mp hD)
  exact ⟨⟨D, by have := C.2; omega⟩, rfl⟩

theorem incl_dLin (n : ℕ) (z : Graded (n + 1) →₀ ℚ) : incl n (dLin n z) = LQ (incl (n + 1) z) := by
  have h : incl n ∘ₗ dLin n = LQ ∘ₗ incl (n + 1) := by
    apply Finsupp.lhom_ext
    intro C a
    have e : (single C a : Graded (n + 1) →₀ ℚ) = a • single C 1 := by simp
    rw [e]
    simp only [LinearMap.comp_apply, map_smul, dLin, linearCombination_single, incl,
      Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, LQ, one_smul]
    congr 1
    refine Finsupp.mapDomain_comapDomain Subtype.val Subtype.val_injective _ ?_
    intro D hD
    have := incQ_grade C.1 D (Finsupp.mem_support_iff.mp hD)
    exact ⟨⟨D, by have := C.2; omega⟩, rfl⟩
  exact LinearMap.congr_fun h z

theorem dLin_dLin (n : ℕ) : dLin n ∘ₗ dLin (n + 1) = 0 := by
  apply LinearMap.ext
  intro z
  apply incl_injective n
  rw [LinearMap.comp_apply, incl_dLin, incl_dLin, ← LinearMap.comp_apply, LQ_LQ]
  simp

/-- The cellular permutation complex of the well-rounded retract (cells of grade `n` in degree `n`;
it vanishes above degree three since cells have grade at most three). -/
def cellPermComplex : ChainComplex (Rep ℚ principalSix) ℕ :=
  ChainComplex.of cellRep cellD (fun n => by
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    change (MonoidAlgebra.coeffLinearEquiv ℚ).symm (dLin n ((MonoidAlgebra.coeffLinearEquiv ℚ)
      ((MonoidAlgebra.coeffLinearEquiv ℚ).symm (dLin (n + 1) ((MonoidAlgebra.coeffLinearEquiv ℚ) z))))) = 0
    rw [LinearEquiv.apply_symm_apply, ← LinearMap.comp_apply, dLin_dLin]
    simp)

/-- An equivariant linear map out of a permutation representation, given on generators. -/
def permHomTo {G : Type} [Group G] {S : Type} [MulAction G S] (W : Rep ℚ G) (L : (S →₀ ℚ) →ₗ[ℚ] W)
    (hL : ∀ (g : G) (C : S), L (single (g • C) 1) = W.ρ g (L (single C 1))) :
    Rep.ofMulAction ℚ G S ⟶ W :=
  Rep.ofHom ⟨L ∘ₗ (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap, fun g => by
    have key : L ∘ₗ Finsupp.lmapDomain ℚ ℚ (g • ·) = W.ρ g ∘ₗ L := by
      apply Finsupp.lhom_ext
      intro C a
      have e : (single C a : S →₀ ℚ) = a • single C 1 := by simp
      rw [e]
      simp only [LinearMap.comp_apply, map_smul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      rw [hL]
    apply LinearMap.ext
    intro z
    simp only [Representation.ofMulAction_def, LinearMap.comp_apply]
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun key _⟩

/-- The degree-`n` component of the cellular chain map. -/
def cellChainF (n : ℕ) : cellRep n ⟶ chainRep principalSix (TopCat.of Glued) n :=
  permHomTo _ (linearCombination ℚ (fun C : Graded n => cellAt n C.1)) (fun g C => by
    simp only [linearCombination_single, one_smul]
    exact cellAt_smul_six g n C.1)

theorem cellChainF_single (n : ℕ) (C : Graded n) :
    (cellChainF n).hom (MonoidAlgebra.single C 1) = cellAt n C.1 := by
  change linearCombination ℚ (fun C : Graded n => cellAt n C.1)
    ((MonoidAlgebra.coeffLinearEquiv ℚ) (MonoidAlgebra.single C 1)) = _
  have h : (MonoidAlgebra.coeffLinearEquiv ℚ) (MonoidAlgebra.single C (1 : ℚ)) =
      (single C 1 : Graded n →₀ ℚ) := rfl
  rw [h, linearCombination_single, one_smul]

theorem cellChainF_hom (n : ℕ) (z : MonoidAlgebra ℚ (Graded n)) :
    (cellChainF n).hom z =
      linearCombination ℚ (fun C : Graded n => cellAt n C.1) (MonoidAlgebra.coeffLinearEquiv ℚ z) :=
  rfl

theorem lin_cellD (j : ℕ) (w : Graded (j + 1) →₀ ℚ) :
    linearCombination ℚ (fun C : Graded j => cellAt j C.1) (dLin j w) =
      ((underlyingChains (TopCat.of Glued)).d (j + 1) j).hom
        (linearCombination ℚ (fun C : Graded (j + 1) => cellAt (j + 1) C.1) w) := by
  have h : (linearCombination ℚ (fun C : Graded j => cellAt j C.1)) ∘ₗ dLin j =
      ((underlyingChains (TopCat.of Glued)).d (j + 1) j).hom ∘ₗ
        linearCombination ℚ (fun C : Graded (j + 1) => cellAt (j + 1) C.1) := by
    apply Finsupp.lhom_ext
    intro C a
    have e : (single C a : Graded (j + 1) →₀ ℚ) = a • single C 1 := by simp
    rw [e]
    simp only [LinearMap.comp_apply, map_smul, dLin, linearCombination_single, one_smul]
    congr 1
    have h1 : linearCombination ℚ (fun D : Graded j => cellAt j D.1) (dGr j C) =
        linearCombination ℚ (cellAt j) (incl j (dGr j C)) := by
      rw [incl, Finsupp.lmapDomain_apply, linearCombination_mapDomain]
      rfl
    rw [h1, incl_dGr, d_cellAt j C.1 C.2]
    rfl
  exact LinearMap.congr_fun h w

/-- **The cellular chain map**: the permutation complex of the cells of the well-rounded retract
maps to the `Γ(6)`-equivariant singular chains of the bordification, by `C ↦ cellAt n C`. -/
def cellChainMap : cellPermComplex ⟶ equivariantChains principalSix (TopCat.of Glued) where
  f := cellChainF
  comm' := by
    intro i j hij
    obtain rfl : j + 1 = i := hij
    have hd : cellPermComplex.d (j + 1) j = cellD j := ChainComplex.of_d _ _ _
    rw [hd]
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro z
    change ((underlyingChains (TopCat.of Glued)).d (j + 1) j).hom
        (linearCombination ℚ (fun C : Graded (j + 1) => cellAt (j + 1) C.1)
          (MonoidAlgebra.coeffLinearEquiv ℚ z)) =
      linearCombination ℚ (fun C : Graded j => cellAt j C.1)
        ((MonoidAlgebra.coeffLinearEquiv ℚ) ((MonoidAlgebra.coeffLinearEquiv ℚ).symm
          (dLin j (MonoidAlgebra.coeffLinearEquiv ℚ z))))
    rw [LinearEquiv.apply_symm_apply]
    exact (lin_cellD j _).symm

/-! ### Coefficients -/

/-- The cellular complex with coefficients: `(cells ⊗ W)_{Γ(6)}`. -/
abbrev cellCoinv (W : Rep ℚ principalSix) : ChainComplex (ModuleCat ℚ) ℕ :=
  cellPermComplex.coinvariantsTensorObj W

/-- The cellular chain map with coefficients in `W`. -/
def cellCoinvMap (W : Rep ℚ principalSix) :
    cellCoinv W ⟶ SingularLocalHomology.coinvariantChains principalSix (TopCat.of Glued) W :=
  (((Rep.coinvariantsTensor ℚ principalSix).obj W).mapHomologicalComplex (ComplexShape.down ℕ)).map
    cellChainMap

/-- The generator `w ⊗ C` goes to the elementary coinvariant chain `w ⊗ cellAt n C`. -/
theorem cellCoinvMap_mk (W : Rep ℚ principalSix) (n : ℕ) (w : W) (C : Graded n) :
    (cellCoinvMap W).f n (Rep.coinvariantsTensorMk W (cellRep n) w (MonoidAlgebra.single C 1)) =
      Rep.coinvariantsTensorMk W (chainRep principalSix (TopCat.of Glued) n) w (cellAt n C.1) := by
  have h := SingularLocalHomology.tensorCoinvariant_map_mk W (cellRep n)
    (chainRep principalSix (TopCat.of Glued) n) (cellChainF n) w (MonoidAlgebra.single C 1)
  rw [cellChainF_single] at h
  exact h

/-- The cellular chain map into the geometric local-coefficient chains of the bordification. -/
def cellToBordified (W : Rep.{0} ℚ principalSix) :
    cellCoinv W ⟶ bordifiedLocalChains W :=
  cellCoinvMap W ≫ (bordifiedChainIso W).hom

/-- **The cellular classes as group homology**: the homology of the cellular complex with coefficients
in `W` maps to `H_n(Γ(6), W)` through the bordification. -/
def cellGroupHomologyMap (W : Rep.{0} ℚ principalSix) (n : ℕ) :
    (cellCoinv W).homology n ⟶ groupHomology W n :=
  HomologicalComplex.homologyMap (cellToBordified W) n ≫ (bordifiedGroupLocalHomologyIso W n).inv

end TernaryPeriodPolynomials.Argument.Lemma33.Retract
