module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Literal.ResidueCycle
public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Literal.DualityNatural
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Prime
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.LiftableResidueObstruction

@[expose] public section


/-!
# Lemma 4.5, sentences 2-3: `𝓛_n` from group homology, the extreme coefficient, and Hecke stability

Formalized by Claude Sonnet 5.5.
Paper: Lemma 4.5 (`lem:residue-period`) and its
proof ("liftable residues are Hecke-stable").

`LnHom n` is the image in `ℬ_{n+1}` (under the literal residue `res_H`) of the image of
`H₃(G, ℳ_n ⊗ det⁻¹) → H₃(G, ℛ_n ⊗ det⁻¹)`, the map induced by the residue `ℳ_n → ℛ_n`.

**Proved.**

* `H3_G_equiv_M`: the Borel-Serre duality for the module `ℳ_n` of single-pole functions;
* `H3_G_equiv_natural`: it is natural with respect to the residue map;
* `LnHom_eq_liftable`: `LnHom n` is the image under the period isomorphism of the library's Hom-model liftable residue
  functionals `liftableResidueHoms n (-1)`;
* `LnHom_extreme`: for `q ∈ LnHom n`, the coefficient of `a c^n` (indeed of every `X Y^m` monomial) vanishes;
* `LnHom_hecke_stable`: `LnHom n` is stable under the homology Hecke operator of `diag(p,1,1)⁻¹`, transported to `ℬ_{n+1}`.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma45Literal

open TernaryPoly TernaryPoly.ModThreeGoodAction IntegralGL3Congruence TernaryPoly.SinglePole
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.GroupHomology
open TernaryPeriodPolynomials.Argument.AppendixBResidue
open TernaryPeriodPolynomials.Argument.HeckeHomology TernaryPoly.SinglePoleCoordinate

/-- `ℳ_n ⊗ det⁻¹` as a `GL₃(ℤ)`-module (the module of single-pole functions, integral action with determinant exponent `-1`). -/
abbrev MRep (n : ℕ) : Rep.{0} ℚ IntegralGL :=
  Rep.res OrdinaryFullAction.integral (Rep.of (singlePoleAction n (-1)))

/-- The residue map `ℳ_n → ℛ_n` as a morphism of `GL₃(ℤ)`-modules. -/
def residueRepG (n : ℕ) : MRep n ⟶ ResRep n :=
  (Rep.resFunctor OrdinaryFullAction.integral).map (residueRep n (-1))

theorem resRep_eq (n : ℕ) : ResRep n = Rep.res OrdinaryFullAction.integral (Rep.of (residueAction n (-1))) := rfl

theorem homKGen_stG_M (n : ℕ) :
    homKGen stG (MRep n) = OrdinaryFullCoefficient.SinglePoleHom n (-1) := by
  ext Φ
  rfl

theorem capEps_M (n : ℕ) (k : IntegralGL) : CapEpsStatement k (MRep n) :=
  TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k (MRep n)

/-- **Borel-Serre duality for `ℳ_n`**: `H₃(G, ℳ_n ⊗ det⁻¹) ≃ Hom_G(St, ℳ_n ⊗ det⁻¹)`. -/
def H3_G_equiv_M (n : ℕ) :
    groupHomology (MRep n) 3 ≃ₗ[ℚ] OrdinaryFullCoefficient.SinglePoleHom n (-1) :=
  (H3GGen (MRep n) (capEps_M n)).trans (LinearEquiv.ofEq _ _ (homKGen_stG_M n))

theorem H3_G_equiv_eq (n : ℕ) :
    H3_G_equiv n = (H3GGen (ResRep n) (fun k => TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k (ResRep n))).trans
      (LinearEquiv.ofEq _ _ (homKGen_stG_eq n)) := rfl

/-- **Naturality of the `G`-level duality along the residue map**: the functional of the residue image of a class is the residue
(postcomposition) of its functional. -/
theorem H3_G_equiv_natural (n : ℕ) (x : groupHomology (MRep n) 3) :
    H3_G_equiv n ((groupHomology.map (MonoidHom.id IntegralGL) (residueRepG n) 3).hom x) =
      OrdinaryFullCoefficient.residueHom n (-1) (H3_G_equiv_M n x) := by
  apply Subtype.ext
  have h := H3GGen_natural (capEps_M n) (fun k => TernaryPeriodPolynomials.Argument.DualityEquivariance.capEps k (ResRep n))
    (residueRepG n) x
  rw [H3_G_equiv_eq]
  exact h

/-- **`𝓛_n` from homology**: the image in `ℬ_{n+1}`, under the literal residue, of the image of
`H₃(G, ℳ_n ⊗ det) → H₃(G, ℛ_n ⊗ det)`. -/
def LnHom (n : ℕ) : Submodule ℚ (OrdinaryResiduePeriod.periodSpace (n + 1)) :=
  (LinearMap.range (groupHomology.map (MonoidHom.id IntegralGL) (residueRepG n) 3).hom).map (resHLit n)

/-- The Hom-model liftable residues `liftableResidueHoms` are exactly the residue functionals of classes of
`H₃(G, ℳ_n ⊗ det)`. -/
theorem map_range_eq_liftable (n : ℕ) :
    (LinearMap.range (groupHomology.map (MonoidHom.id IntegralGL) (residueRepG n) 3).hom).map
        (H3_G_equiv n).toLinearMap = OrdinaryFullCoefficient.liftableResidueHoms n (-1) := by
  rw [← LinearMap.range_comp]
  have h : ((H3_G_equiv n).toLinearMap ∘ₗ (groupHomology.map (MonoidHom.id IntegralGL) (residueRepG n) 3).hom) =
      (OrdinaryFullCoefficient.residueHom n (-1)) ∘ₗ (H3_G_equiv_M n).toLinearMap := by
    exact LinearMap.ext fun x => H3_G_equiv_natural n x
  rw [h, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]
  rfl

theorem resHLit_eq_comp (n : ℕ) :
    resHLit n = (OrdinaryResiduePeriod.periodEquiv n).toLinearMap ∘ₗ (H3_G_equiv n).toLinearMap :=
  LinearMap.ext fun x => by
    apply Subtype.ext
    exact (congrArg Subtype.val (resH_eq_periodEquiv n (H3_G_equiv n x))).symm

/-- **`𝓛_n` is the image of the Hom-model liftable residues**: the homology definition and the library's
`liftableResidueHoms` agree under the period isomorphism. -/
theorem LnHom_eq_liftable (n : ℕ) :
    LnHom n = (OrdinaryFullCoefficient.liftableResidueHoms n (-1)).map
      (OrdinaryResiduePeriod.periodEquiv n).toLinearMap := by
  unfold LnHom
  rw [resHLit_eq_comp, Submodule.map_comp, map_range_eq_liftable]

theorem mem_LnHom_iff (n : ℕ) (q : OrdinaryResiduePeriod.periodSpace (n + 1)) :
    q ∈ LnHom n ↔ ∃ Φ ∈ OrdinaryFullCoefficient.liftableResidueHoms n (-1),
      OrdinaryResiduePeriod.periodEquiv n Φ = q := by
  rw [LnHom_eq_liftable]
  exact Submodule.mem_map

/-- **The extreme coefficient vanishes on `𝓛_n`**: `[X Y^m] q = 0`, the coefficient of the monomial `X^1 Y^m`. -/
theorem LnHom_extreme (n : ℕ) (q : OrdinaryResiduePeriod.periodSpace (n + 1)) (hq : q ∈ LnHom n)
    (m : Fin 1 →₀ ℕ) : (q.val : BinaryV (n + 1)).val.coeff (Finsupp.cons 1 m) = 0 := by
  obtain ⟨Φ, hΦ, rfl⟩ := (mem_LnHom_iff n q).1 hq
  exact OrdinaryFullCoefficient.liftable_coordinate_extreme n Φ hΦ 0 m

/-- The literal statement `[a c^n] q(a,c) = 0` for `q ∈ 𝓛_n`. -/
theorem LnHom_extreme_literal (n : ℕ) (q : OrdinaryResiduePeriod.periodSpace (n + 1)) (hq : q ∈ LnHom n) :
    (q.val : BinaryV (n + 1)).val.coeff (Finsupp.single 0 1 + Finsupp.single 1 n) = 0 := by
  have h : (Finsupp.single 0 1 + Finsupp.single 1 n : Fin 2 →₀ ℕ) = Finsupp.cons 1 (Finsupp.single 0 n) := by
    ext i
    fin_cases i
    · simp
    · have h1 : ((1 : Fin 2)) = Fin.succ 0 := rfl
      simp only [Fin.mk_one, h1, Finsupp.cons_succ]
      simp
  rw [h]
  exact LnHom_extreme n q hq _

/-- The homology Hecke operator `T₃(p,1)` of `diag(p,1,1)⁻¹` on `H₃(G, ℛ_n ⊗ det⁻¹)`. -/
def T3 (p : ℕ) [Fact p.Prime] (n : ℕ) : groupHomology (ResRep n) 3 →ₗ[ℚ] groupHomology (ResRep n) 3 :=
  (heckeOp (primeDatum p) (Rep.of (residueAction n (-1))) 3).hom

/-- `T₃(p,1)` transported to the period space `ℬ_{n+1}` by the literal residue. -/
def T3B (p : ℕ) [Fact p.Prime] (n : ℕ) :
    OrdinaryResiduePeriod.periodSpace (n + 1) →ₗ[ℚ] OrdinaryResiduePeriod.periodSpace (n + 1) :=
  (resHLitEquiv n).toLinearMap ∘ₗ T3 p n ∘ₗ (resHLitEquiv n).symm.toLinearMap

theorem mem_LnHom_iff_hom (n : ℕ) (q : OrdinaryResiduePeriod.periodSpace (n + 1)) :
    q ∈ LnHom n ↔ (resHLitEquiv n).symm q ∈
      LinearMap.range (groupHomology.map (MonoidHom.id IntegralGL) (residueRepG n) 3).hom := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← resHLitEquiv_apply, LinearEquiv.symm_apply_apply]
    exact hx
  · intro h
    exact ⟨_, h, (resHLitEquiv_apply n _).symm.trans ((resHLitEquiv n).apply_symm_apply q)⟩

/-- **Hecke stability of `𝓛_n` for the homology operator `T₃(p,1)`** ("liftable residues are Hecke-stable"):
the image of `H₃(G, ℳ_n ⊗ det) → H₃(G, ℛ_n ⊗ det)` is stable under the homology Hecke operator of `diag(p,1,1)⁻¹`, hence `𝓛_n`
is stable under its transport `T3B p n` to the period space. -/
theorem LnHom_hecke_stable (p : ℕ) [Fact p.Prime] (n : ℕ) (q : OrdinaryResiduePeriod.periodSpace (n + 1))
    (hq : q ∈ LnHom n) : T3B p n q ∈ LnHom n := by
  rw [mem_LnHom_iff_hom] at hq ⊢
  have h := liftableHomology_stable p n (-1) ((resHLitEquiv n).symm q) hq
  have e : (resHLitEquiv n).symm (T3B p n q) = T3 p n ((resHLitEquiv n).symm q) := by simp [T3B]
  rw [e]
  exact h

end TernaryPeriodPolynomials.Argument.Lemma45Literal
