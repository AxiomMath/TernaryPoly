module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Hecke
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.CosetsDiagonal
public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.Equivariance
public import TernaryPeriodPolynomials.SymmetricSolution.SinglePole.SupportTransport
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.Action

@[expose] public section


/-!
# Prime Hecke datum for `diag(p,1,1)⁻¹` and Hecke stability of the homology-level liftable residues

Formalized by Claude Sonnet 5.5.

The homology Hecke operator `[Γ g Γ]` of `Proofs/HeckeHomology/Hecke.lean` is instantiated for
`Γ = GL₃(ℤ) ⊂ GL₃(ℚ)` and `g = diag(p,1,1)⁻¹`.  Its commensurated subgroup is
`{k | p ∣ k₀₁ ∧ p ∣ k₀₂}`, of finite index because it contains the kernel of reduction mod `p`.
Naturality in the coefficient module gives: the image of `H₃(GL₃(ℤ), singlePole) → H₃(GL₃(ℤ), 𝓡_n)`
(the homology liftable residues) is stable under this operator.
-/

open CategoryTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

variable {Γ Ĝ : Type} [Group Γ] [Group Ĝ]

/-- The Hecke datum of a commensurating element: `S = {γ | g ι(γ) g⁻¹ ∈ ι(Γ)}` for injective `ι`. -/
def commSubgroup (ι : Γ →* Ĝ) (g : Ĝ) : Subgroup Γ where
  carrier := {γ | ∃ δ : Γ, ι δ = g * ι γ * g⁻¹}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    exact ⟨a' * b', by rw [map_mul, ha, hb, map_mul]; group⟩
  inv_mem' := by
    rintro a ⟨a', ha⟩
    exact ⟨a'⁻¹, by rw [map_inv, ha, map_inv]; group⟩

theorem mem_commSubgroup {ι : Γ →* Ĝ} {g : Ĝ} {γ : Γ} :
    γ ∈ commSubgroup ι g ↔ ∃ δ : Γ, ι δ = g * ι γ * g⁻¹ := Iff.rfl

/-- The Hecke datum with the full commensurator subgroup. -/
def HeckeDatum.ofInjective {ι : Γ →* Ĝ} (hι : Function.Injective ι) (g : Ĝ)
    (hfin : (commSubgroup ι g).FiniteIndex) : HeckeDatum ι g where
  S := commSubgroup ι g
  finiteIndex := hfin
  f :=
    { toFun := fun s => Classical.choose s.2
      map_one' := by
        apply hι
        rw [Classical.choose_spec (1 : commSubgroup ι g).2]
        simp
      map_mul' := fun s t => by
        apply hι
        rw [map_mul, Classical.choose_spec s.2, Classical.choose_spec t.2,
          Classical.choose_spec (s * t).2]
        simp only [Subgroup.coe_mul, map_mul]
        group }
  hf s := Classical.choose_spec s.2

end TernaryPeriodPolynomials.Argument.HeckeHomology

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryFullAction
  TernaryPoly.OrdinaryHeckeCosets TernaryPoly.OrdinaryHeckeArithmetic TernaryPoly.OrdinaryHeckeTransfer

/-- `ι_p := diag(p, 1, 1)⁻¹`: the element `g = t⁻¹` of the homology Hecke datum realizing the paper's RIGHT correspondence
of `t = diag(p,1,1)` (proved in `DictionaryDatum.lean`: `primeDatum_t`, `primeDatum_right_conj`, `primeDatum_corrMap`).
Its relation to any Hom-model operator under Poincaré–Borel–Serre duality is NOT established here (that comparison is the bridge, cf. `Proofs/HeckeNormalization/Bridge.lean`). -/
def gInv (p : ℕ) [Fact p.Prime] : GL3 := (primeDiagonal p)⁻¹

theorem mem_commSubgroup_gInv (p : ℕ) [Fact p.Prime] (k : IntegralGL) :
    k ∈ commSubgroup OrdinaryFullAction.integral (gInv p) ↔ (p : ℤ) ∣ k.val 0 1 ∧ (p : ℤ) ∣ k.val 0 2 := by
  rw [← mem_primeIntersection_iff, mem_intersection]
  change (∃ δ : IntegralGL, OrdinaryFullAction.integral δ = (primeDiagonal p)⁻¹ * OrdinaryFullAction.integral k * ((primeDiagonal p)⁻¹)⁻¹) ↔
    (primeDiagonal p)⁻¹ * (integralEquiv k).val * primeDiagonal p ∈ Gamma
  rw [inv_inv]
  constructor
  · rintro ⟨δ, hδ⟩
    exact ⟨δ, hδ⟩
  · rintro ⟨δ, hδ⟩
    exact ⟨δ, hδ⟩


/-- The reduction-mod-`p` kernel lies in the commensurator subgroup, which therefore has finite index. -/
theorem finiteIndex_commSubgroup_gInv (p : ℕ) [Fact p.Prime] :
    (commSubgroup OrdinaryFullAction.integral (gInv p)).FiniteIndex := by
  let red : IntegralGL →* GL (Fin 3) (ZMod p) :=
    Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod p))
  have : Finite (GL (Fin 3) (ZMod p)) := inferInstance
  have : red.ker.FiniteIndex := Subgroup.finiteIndex_ker red
  refine Subgroup.finiteIndex_of_le (H := red.ker) ?_
  intro k hk
  rw [mem_commSubgroup_gInv]
  have h01 := congrArg (fun m : GL (Fin 3) (ZMod p) => (m : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 1) (MonoidHom.mem_ker.mp hk)
  have h02 := congrArg (fun m : GL (Fin 3) (ZMod p) => (m : Matrix (Fin 3) (Fin 3) (ZMod p)) 0 2) (MonoidHom.mem_ker.mp hk)
  simp [red, Matrix.GeneralLinearGroup.map] at h01 h02
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h01, (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h02⟩


theorem integral_injective' : Function.Injective (OrdinaryFullAction.integral) := by
  intro g h he
  apply Units.ext
  ext i j
  have e := congrArg (fun r : GL3 => r.val i j) he
  change (g.val i j : ℚ) = (h.val i j : ℚ) at e
  exact_mod_cast e

/-- The prime Hecke datum of `diag(p,1,1)⁻¹` on `GL₃(ℤ) ⊂ GL₃(ℚ)`. -/
def primeDatum (p : ℕ) [Fact p.Prime] : HeckeDatum OrdinaryFullAction.integral (gInv p) :=
  HeckeDatum.ofInjective integral_injective' (gInv p) (finiteIndex_commSubgroup_gInv p)

open TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport in
/-- The residue map as a morphism of `GL₃(ℚ)`-modules. -/
def residueRep (n : ℕ) (e : ℤ) :
    Rep.of (singlePoleAction n e) ⟶ Rep.of (residueAction n e) :=
  Rep.ofHom ⟨residue n, fun g => LinearMap.ext fun x => (residue_equivariant n e g x).symm⟩

open TernaryPoly.SinglePole TernaryPoly.SinglePoleSupport in
/-- **Hecke stability of the homology liftable residues.**  The image of
`H₃(GL₃(ℤ), singlePole) → H₃(GL₃(ℤ), 𝓡_n)` induced by the residue map is stable under the homology
Hecke operator of `diag(p,1,1)⁻¹`. -/
theorem liftableHomology_stable (p : ℕ) [Fact p.Prime] (n : ℕ) (e : ℤ)
    (x : groupHomology (Rep.res OrdinaryFullAction.integral (Rep.of (residueAction n e))) 3)
    (hx : x ∈ LinearMap.range (groupHomology.map (MonoidHom.id IntegralGL)
      ((Rep.resFunctor OrdinaryFullAction.integral).map (residueRep n e)) 3).hom) :
    (heckeOp (primeDatum p) (Rep.of (residueAction n e)) 3).hom x ∈ LinearMap.range
      (groupHomology.map (MonoidHom.id IntegralGL)
        ((Rep.resFunctor OrdinaryFullAction.integral).map (residueRep n e)) 3).hom :=
  range_heckeOp_stable (primeDatum p) (residueRep n e) 3 x hx

end TernaryPeriodPolynomials.Argument.HeckeHomology
