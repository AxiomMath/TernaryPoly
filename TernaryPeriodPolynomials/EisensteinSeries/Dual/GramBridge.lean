module

public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.GramCochain
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.ComplexifyGen
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.GammaNSeries
public import TernaryPeriodPolynomials.EisensteinSeries.Dual.Cuspidal

@[expose] public section


open scoped Matrix.Norms.Elementwise MatrixGroups ContDiff
open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous

/-!
# The dual series is represented by a homogeneous cocycle on `GL₃(ℝ)`-vertices

Formalized by Claude Sonnet 5.5.

the `FormSeriesModel.bridge_gramCocycle_eisenstein` represents the complexified class of the series `ℰ_P(ω_f)` by the
Gram-triangle cocycle `F(y₀,y₁,y₂) = ∫_{[y_iy_iᵗ]} φ^*ω` of the homogeneous model on `GL₃(ℝ)`-vertices.  Here the dual analogue:

* `jReal` (`ȷ(g) = rt (g⁻¹) = J (g⁻¹)ᵗ J` on `GL₃(ℝ)`, extending `ȷ` of `SL₃(ℤ)`: `jReal_mapGL`), and the dual coefficient system `dualRealCoeff n = ρ_ℂ ∘ ȷ`;
* `jRealCocycle`: the cocycle `F^∨(y) = F(ȷ y₀, ȷ y₁, ȷ y₂)` of the level `realLevel Γ(N)` for `ρ_ℂ ∘ ȷ`;
* `bridge_dual_gram`: for EVERY closed `Γ(N)`-equivariant form `ω`, the complexified class of `ȷ̃^* ω` in `H²(Γ(N), E^∨)` is the bridge of `F^∨` with `F` the Gram
  cocycle of `ω` (naturality of the bridge under the automorphism `ȷ`, the `bridge_gramCocycle` and `cxGen_map`);
* `dual_series_gram`, `dual_series_at_gram`: the same for the actual dual series `ℰ_Q^∨` (standard cusp) and at the plane cusp `ȷ(h)` with seed type `b`.

NOT proved: the passage from `GL₃(ℝ)`-vertices to the rational cocycle model of `rationalLevel` is not established for the series `ℰ_P` itself; this file gives the dual bridge exactly to the level where the plane bridge exists.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument.GammaNFaces (rt rt_mul rt_one rt_rt)
open TernaryPeriodPolynomials.Argument.ConvergenceC4

/-- **`ȷ` on `GL₃(ℝ)`**: `ȷ(g) = rt (g⁻¹) = J (g⁻¹)ᵗ J`, an involutive automorphism extending `ȷ` of `SL₃(ℤ)`. -/
def jReal : RealGL3 →* RealGL3 where
  toFun g :=
    { val := rt ((g⁻¹ : RealGL3) : Matrix (Fin 3) (Fin 3) ℝ)
      inv := rt (g : Matrix (Fin 3) (Fin 3) ℝ)
      val_inv := by
        rw [← rt_mul, ← Units.val_mul, mul_inv_cancel]
        exact rt_one
      inv_val := by
        rw [← rt_mul, ← Units.val_mul, inv_mul_cancel]
        exact rt_one }
  map_one' := by
    apply Units.ext
    simp [rt_one]
  map_mul' a b := by
    apply Units.ext
    change rt (((a * b)⁻¹ : RealGL3) : Matrix (Fin 3) (Fin 3) ℝ) = _
    rw [_root_.mul_inv_rev, Units.val_mul, rt_mul]
    rfl

theorem jReal_val (g : RealGL3) :
    ((jReal g : RealGL3) : Matrix (Fin 3) (Fin 3) ℝ) = rt ((g⁻¹ : RealGL3) : Matrix (Fin 3) (Fin 3) ℝ) := rfl

theorem jReal_mapGL (γ : SL(3, ℤ)) :
    jReal (Matrix.SpecialLinearGroup.mapGL ℝ γ) = Matrix.SpecialLinearGroup.mapGL ℝ (jmath γ) := by
  apply Units.ext
  rw [jReal_val, ← map_inv, TernaryPeriodPolynomials.Argument.FormSeriesModel.mapGL_val, TernaryPeriodPolynomials.Argument.FormSeriesModel.mapGL_val]
  ext i j
  simp [realMat_apply, coe_jmath, rt]


open TernaryPeriodPolynomials.Argument.FormSeriesModel (realLevel realLevelHom gramCocycle repMorReal)

/-- The coefficient representation of the dual homogeneous model: `ρ_ℂ ∘ ȷ`. -/
def dualRealCoeff (n : ℕ) : Representation ℂ RealGL3 (HomogeneousPoly n) := (realCoefficient n).comp jReal

theorem jv (a b c : RealGL3) : (fun i => jReal (![a, b, c] i)) = ![jReal a, jReal b, jReal c] := by
  funext i
  fin_cases i <;> rfl

theorem realLevel_mem {N : ℕ} {γ : RealGL3} (hγ : γ ∈ realLevel (gammaN N)) :
    ∃ g ∈ gammaN N, Matrix.SpecialLinearGroup.mapGL ℝ g = γ := hγ

variable (N n : ℕ)

/-- **The dual homogeneous cocycle** `F^∨(y) = F(ȷ y₀, ȷ y₁, ȷ y₂)` of the level `realLevel Γ(N)` with coefficients `ρ_ℂ ∘ ȷ`. -/
def jRealCocycle (F : cocycles (realLevel (gammaN N)) (realCoefficient n)) :
    cocycles (realLevel (gammaN N)) (dualRealCoeff n) :=
  ⟨⟨fun x => F.val.val (fun i => jReal (x i)), by
    intro γ x
    obtain ⟨g, hg, hγ⟩ := realLevel_mem γ.2
    have hj : jReal γ.val = Matrix.SpecialLinearGroup.mapGL ℝ (jmath g) := by
      rw [← hγ, jReal_mapGL]
    have h1 := F.val.property
      ⟨Matrix.SpecialLinearGroup.mapGL ℝ (jmath g), ⟨jmath g, jmath_mem_gammaN.2 hg, rfl⟩⟩ (fun i => jReal (x i))
    have h2 : (fun i => jReal (γ.val * x i)) = fun i => Matrix.SpecialLinearGroup.mapGL ℝ (jmath g) * jReal (x i) := by
      funext i
      rw [map_mul, hj]
    change F.val.val (fun i => jReal (γ.val * x i)) = realCoefficient n (jReal γ.val) (F.val.val (fun i => jReal (x i)))
    rw [h2, hj]
    exact h1⟩, by
    change differentialTwo _ _ _ = 0
    funext x
    have h := congrFun F.property (fun i => jReal (x i))
    change F.val.val ![jReal (x 1), jReal (x 2), jReal (x 3)] - F.val.val ![jReal (x 0), jReal (x 2), jReal (x 3)] +
      F.val.val ![jReal (x 0), jReal (x 1), jReal (x 3)] - F.val.val ![jReal (x 0), jReal (x 1), jReal (x 2)] = 0 at h
    change F.val.val (fun i => jReal (![x 1, x 2, x 3] i)) - F.val.val (fun i => jReal (![x 0, x 2, x 3] i)) +
      F.val.val (fun i => jReal (![x 0, x 1, x 3] i)) - F.val.val (fun i => jReal (![x 0, x 1, x 2] i)) = 0
    simp only [jv]
    exact h⟩


theorem dualRhoC_eq (g : gammaN N) :
    dualRhoC N n g = ((dualRealCoeff n).comp (realLevel (gammaN N)).subtype) (realLevelHom (gammaN N) g) := by
  change realCoefficient n (Matrix.SpecialLinearGroup.mapGL ℝ (jmath g.1)) = realCoefficient n (jReal (Matrix.SpecialLinearGroup.mapGL ℝ g.1))
  rw [jReal_mapGL]

open CategoryTheory groupCohomology in
/-- The comparison `Res_φ (ρ_ℂ ∘ ȷ |_{realLevel}) → ρ_ℂ ∘ ȷ` of the dual coefficient modules. -/
def repMorDual : Rep.res (realLevelHom (gammaN N))
    (Rep.of ((dualRealCoeff n).comp (realLevel (gammaN N)).subtype)) ⟶ Rep.of (dualRhoC N n) :=
  resMorK (realLevelHom (gammaN N)) (dualRhoC N n) ((dualRealCoeff n).comp (realLevel (gammaN N)).subtype)
    (dualRhoC_eq N n)


open CategoryTheory groupCohomology TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.SeedC3 in
theorem cxGen_eq_complexify (Γ : Subgroup SL(3, ℤ)) (x : H2 (Rep.of (gammaRho Γ n))) :
    cxGen (gammaRho Γ n) (gammaRhoC Γ n) (fun _ _ => rfl) x = complexify Γ n x := by
  induction x using H2_induction_on with
  | _ c =>
    exact (cxGen_H2π (gammaRho Γ n) (gammaRhoC Γ n) (fun _ _ => rfl) c).trans (complexify_H2π Γ n c).symm

open CategoryTheory groupCohomology TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.SeedC3 TernaryPoly.SmoothLocalDeRham in
/-- **The dual series is represented by a homogeneous cocycle on `GL₃(ℝ)`-vertices.**  For every closed `Γ(N)`-equivariant form `ω`
(for the series, `ω = ℰ_P(ω_f)`), the complexified class of `ȷ̃^* ω` in `H²(Γ(N), E^∨)` is the bridge of the homogeneous cocycle
`F^∨(y) = F(ȷ y₀, ȷ y₁, ȷ y₂)`, `F` the Gram-triangle cocycle of `ω` (S7's `gramCocycle`), under `LevelTransfer.bridge` and `Γ(N) ≅ realLevel`. -/
theorem bridge_dual_gram
    (om : ZigZag.invClosed isOpen_Omega (gammaAct (gammaN N)) (gammaRho (gammaN N) n)) :
    (groupCohomology.map (realLevelHom (gammaN N)) (repMorDual N n) 2).hom
        (TernaryPeriodPolynomials.Argument.LevelTransfer.bridge (dualRealCoeff n) (realLevel (gammaN N))
          (Submodule.Quotient.mk (jRealCocycle N n (gramCocycle (gammaN N) n om)))) =
      cxGen (dualRhoN N n) (dualRhoC N n) (fun _ _ => rfl)
        (ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct (gammaN N)) (dualRhoN N n)
          (pullInv (jEquivMap (gammaN N) (gammaN N) (jN N) (fun _ => rfl)) (fun _ => rfl) om)) := by
  rw [TernaryPeriodPolynomials.Argument.EisensteinClass.deRhamClass_natural (jEquivMap (gammaN N) (gammaN N) (jN N) (fun _ => rfl))
    convex_Omega Omega_nonempty convex_Omega Omega_nonempty (fun _ => rfl) om]
  rw [cxGen_map (dualRhoN N n) (dualRhoC N n) (fun _ _ => rfl) (gammaRho (gammaN N) n) (gammaRhoC (gammaN N) n) (fun _ _ => rfl)
    (jN N) (fun _ => rfl) (fun _ => rfl), cxGen_eq_complexify]
  rw [← TernaryPeriodPolynomials.Argument.FormSeriesModel.bridge_gramCocycle (gammaN N) n om]
  rw [TernaryPeriodPolynomials.Argument.LevelTransfer.bridge_mk, TernaryPeriodPolynomials.Argument.LevelTransfer.bridge_mk]
  rw [groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply, groupCohomology.H2π_comp_map_apply]
  refine congrArg (H2π (Rep.of (dualRhoC N n))).hom ?_
  apply Subtype.ext
  funext p
  change (TernaryPeriodPolynomials.Argument.LevelTransfer.bridgeCocycle (dualRealCoeff n) (realLevel (gammaN N))
      (jRealCocycle N n (gramCocycle (gammaN N) n om)) : realLevel (gammaN N) × realLevel (gammaN N) → HomogeneousPoly n)
      (realLevelHom (gammaN N) p.1, realLevelHom (gammaN N) p.2) =
    (TernaryPeriodPolynomials.Argument.LevelTransfer.bridgeCocycle (realCoefficient n) (realLevel (gammaN N))
      (gramCocycle (gammaN N) n om) : realLevel (gammaN N) × realLevel (gammaN N) → HomogeneousPoly n)
      (realLevelHom (gammaN N) (jN N p.1), realLevelHom (gammaN N) (jN N p.2))
  rw [TernaryPeriodPolynomials.Argument.LevelTransfer.bridgeCocycle_apply, TernaryPeriodPolynomials.Argument.LevelTransfer.bridgeCocycle_apply]
  change (gramCocycle (gammaN N) n om).val.val (fun i => jReal (![1, (realLevelHom (gammaN N) p.1 : RealGL3),
      ((realLevelHom (gammaN N) p.1 * realLevelHom (gammaN N) p.2 : realLevel (gammaN N)) : RealGL3)] i)) = _
  rw [jv]
  refine congrArg (gramCocycle (gammaN N) n om).val.val ?_
  funext i
  fin_cases i
  · simp
  · change jReal (Matrix.SpecialLinearGroup.mapGL ℝ p.1.1) = Matrix.SpecialLinearGroup.mapGL ℝ (jmath p.1.1)
    rw [jReal_mapGL]
  · change jReal (Matrix.SpecialLinearGroup.mapGL ℝ p.1.1 * Matrix.SpecialLinearGroup.mapGL ℝ p.2.1) =
      Matrix.SpecialLinearGroup.mapGL ℝ (jmath p.1.1) * Matrix.SpecialLinearGroup.mapGL ℝ (jmath p.2.1)
    rw [map_mul, jReal_mapGL, jReal_mapGL]

open TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.SeedC3 in
/-- **The dual series `ℰ_Q^∨` of `Γ(N)` is represented by the homogeneous cocycle `F^∨` on `GL₃(ℝ)`-vertices**
(`F` the Gram-triangle cocycle of `ℰ_P(ω_f)`). -/
theorem dual_series_gram [NeZero N] (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) :
    (groupCohomology.map (realLevelHom (gammaN N)) (repMorDual N n) 2).hom
        (TernaryPeriodPolynomials.Argument.LevelTransfer.bridge (dualRealCoeff n) (realLevel (gammaN N))
          (Submodule.Quotient.mk (jRealCocycle N n (gramCocycle (gammaN N) n
            (planeEisensteinInv (gammaN N) (leviGroup N) n f hn (leviIn_gammaN N)))))) =
      cxGen (dualRhoN N n) (dualRhoC N n) (fun _ _ => rfl) (dualSeriesClass_gammaN N n f hn) :=
  bridge_dual_gram N n _

open TernaryPeriodPolynomials.Argument.Statements.EisensteinClass TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.SeedC3 in
/-- The same for the dual series at the line cusp `h⁻¹ Q h` (`ȷ̃^*` of the series at the plane cusp `ȷ(h)`) and the seed of type `b`. -/
theorem dual_series_at_gram [NeZero N] (f : CuspForm (leviGroup N) ((n + 3 : ℕ) : ℤ)) (hn : 4 ≤ n) (b : Bool) (h : SL(3, ℤ)) :
    (groupCohomology.map (realLevelHom (gammaN N)) (repMorDual N n) 2).hom
        (TernaryPeriodPolynomials.Argument.LevelTransfer.bridge (dualRealCoeff n) (realLevel (gammaN N))
          (Submodule.Quotient.mk (jRealCocycle N n (gramCocycle (gammaN N) n
            (planeEisensteinAtInv b (CuspData.ofSL (jmath h)) (gammaN N) (leviGroup N) n f hn
              (leviInCusp_gammaN N (jmath h))))))) =
      cxGen (dualRhoN N n) (dualRhoC N n) (fun _ _ => rfl)
        (dualSeriesAtClass (gammaN N) (gammaN N) (jN N) (fun _ => rfl) (leviGroup N) n f hn b (CuspData.ofSL (jmath h))
          (leviInCusp_gammaN N (jmath h))) :=
  bridge_dual_gram N n _

end TernaryPeriodPolynomials.Argument.EisensteinDual
