module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.Refutation
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Assembly

@[expose] public section


/-!
# What remains to compare the paper's homology `T₂(p)` with the analytic `T_p` (statements H-1, H-2)

Formalized by Claude Sonnet 5.5.

And `eq:Hecke-formula`.  The paper's `T₂(p)` is the homology correspondence
`TernaryPeriodPolynomials.Argument.HeckeHomology.hecke2 p d = heckeOp (binDatum p) (binMod d) 1` on
`H₁(GL₂(ℤ), Sym^d)` (the `AssemblyConventions` explains the dictionary with the printed right-module
conventions `q ↦ det(C) q(C(b,c))`, with no extra scalar).

* `homologyT2 p d`: that operator transported to `periodSpace d` by the standard-edge coefficient
  `FareyTree.periodEquivHomology`.
* `HomologyHomBridge p d c` (not proved here): `homologyT2 p d = c • periodHecke d (diag(p,1))`,
  where `periodHecke` is the library's exponent-`-1` Hom-model operator on the same period space.
* `homologyComplexT2`: the complexification, acting on the target of `periodMap`.

Proved here (conditional on the visible hypothesis `HomologyHomBridge`; `periodMap_hecke` is the only analytic input):

* `homology_periodMap_of_bridge` (**H-2 from H-1**): `homologyComplexT2 (periodMap f) = c p^{-(d+1)} • periodMap (T_p f)`;
* `homology_printed_sentence_of_bridge`: if `c = p^{d+1}` the printed sentence is TRUE for the homology operator;
* `bridge_scalar_of_printed_sentence`: conversely, if the sentence holds for the homology operator and `T_p f ≠ 0`
  for some `f`, then `c = p^{d+1}`.

Nothing here proves `HomologyHomBridge` for any `c`; the hand derivation predicts
`c = p^{d+1}` (adjointness of `heckeOp` with the Eichler-Shimura cohomological `T_p`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

open TernaryPoly TernaryPoly.BinaryComplexPeriod TernaryPoly.BinaryCuspPeriod
open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeHomology

/-- The paper's homology `T₂(p)` (`hecke2`), transported to the period space by the standard-edge
coefficient of the dual Farey tree. -/
def homologyT2 (p d : ℕ) [Fact p.Prime] : Module.End ℚ (OrdinaryResiduePeriod.periodSpace d) :=
  (periodEquivHomology d).toLinearMap.comp
    ((hecke2 p d).comp (periodEquivHomology d).symm.toLinearMap)

/-- **Statement H-1** (proved for every prime and degree with `c = p^(d+1)`,
`BridgeFinal.homologyHomBridge_holds`): the homology `T₂(p)` is the scalar `c` times the library's exponent-`-1`
Hom-model operator `periodHecke d (diag(p,1))` on the common period space. -/
def HomologyHomBridge (p d : ℕ) [Fact p.Prime] (c : ℚ) : Prop :=
  homologyT2 p d = c • BinaryRationalHecke.periodHecke d (BinaryRationalHeckePrime.primeDiagonal p)

/-- The homology `T₂(p)` on the rational period coordinates `BinaryComplexPeriod.space ℚ d`. -/
def homologyRationalT2 (p d : ℕ) [Fact p.Prime] : Module.End ℚ (space ℚ d) :=
  (rationalEquiv d).toLinearMap.comp
    ((homologyT2 p d).comp (rationalEquiv d).symm.toLinearMap)

/-- The homology `T₂(p)`, complexified to the target of `periodMap`. -/
def homologyComplexT2 (p d : ℕ) [Fact p.Prime] : Module.End ℂ (space ℂ d) :=
  complexifyEnd d (homologyRationalT2 p d)

theorem homologyRationalT2_of_bridge {p d : ℕ} [Fact p.Prime] {c : ℚ} (h : HomologyHomBridge p d c) :
    homologyRationalT2 p d = c • rationalSymbolHecke d (BinaryRationalHeckePrime.primeDiagonal p) := by
  apply LinearMap.ext
  intro q
  have h' : homologyT2 p d ((rationalEquiv d).symm q) =
      c • BinaryRationalHecke.periodHecke d (BinaryRationalHeckePrime.primeDiagonal p)
        ((rationalEquiv d).symm q) := by
    rw [h]; rfl
  simp [homologyRationalT2, rationalSymbolHecke, h']

theorem extend_rat_smul (d : ℕ) (c : ℚ) (q : space ℚ d) :
    extend (algebraMap ℚ ℂ) d (c • q) = (c : ℂ) • extend (algebraMap ℚ ℂ) d q := by
  apply Subtype.ext
  change MvPolynomial.map (algebraMap ℚ ℂ) (c • q.val) = (c : ℂ) • MvPolynomial.map (algebraMap ℚ ℂ) q.val
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  simp [MvPolynomial.algebraMap_eq, MvPolynomial.map_C]

theorem homologyComplexT2_of_bridge {p d : ℕ} [Fact p.Prime] {c : ℚ} (h : HomologyHomBridge p d c) :
    homologyComplexT2 p d = (c : ℂ) • complexHecke d (BinaryRationalHeckePrime.primeDiagonal p) := by
  apply end_ext_on_rational
  intro q
  have h1 : homologyComplexT2 p d (extend (algebraMap ℚ ℂ) d q) =
      extend (algebraMap ℚ ℂ) d (homologyRationalT2 p d q) := complexifyEnd_extend d _ q
  rw [h1, homologyRationalT2_of_bridge h, LinearMap.smul_apply, LinearMap.smul_apply, complexHecke_extend]
  exact extend_rat_smul d c _

/-- **H-2 from H-1.**  Granting `HomologyHomBridge p d c`, the paper's homology `T₂(p)` acts on the
analytic period of a level-one cusp form of weight `d + 2` as `c p^{-(d+1)}` times the period of `T_p f`. -/
theorem homology_periodMap_of_bridge {p d : ℕ} [Fact p.Prime] {c : ℚ} (h : HomologyHomBridge p d c)
    (hd : Even d) (f : Forms d) :
    homologyComplexT2 p d (periodMap d hd f) =
      ((c : ℂ) * (p : ℂ) ^ (-((d : ℤ) + 1))) • periodMap d hd (BinaryCuspHeckeEndomorphism.T d p f) := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [homologyComplexT2_of_bridge h, LinearMap.smul_apply, periodMap_hecke hd f p, smul_smul]
  congr 1
  rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hp]
  simp

/-- If `c = p^{d+1}`, the printed sentence
holds for the paper's homology operator: `T₂(p) (periodMap f) = periodMap (T_p f)`. -/
theorem homology_printed_sentence_of_bridge {p d : ℕ} [Fact p.Prime]
    (h : HomologyHomBridge p d ((p : ℚ) ^ (d + 1))) (hd : Even d) (f : Forms d) :
    homologyComplexT2 p d (periodMap d hd f) =
      periodMap d hd (BinaryCuspHeckeEndomorphism.T d p f) := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [homology_periodMap_of_bridge h hd f]
  have : (((p : ℚ) ^ (d + 1) : ℚ) : ℂ) * (p : ℂ) ^ (-((d : ℤ) + 1)) = 1 := by
    push_cast
    rw [← zpow_natCast, ← zpow_add₀ hp]
    simp
  rw [this, one_smul]

/-- **Statement H-2** (proved, `BridgeFinal.homologyPrintedSentence_holds`): the printed sentence of the paper
for the paper's homology operator:
`T₂(p) (periodMap f) = periodMap (T_p f)` for every level-one cusp form `f` of weight `d + 2`. -/
def HomologyPrintedSentence (p d : ℕ) [Fact p.Prime] (hd : Even d) : Prop :=
  ∀ f : Forms d, homologyComplexT2 p d (periodMap d hd f) =
    periodMap d hd (BinaryCuspHeckeEndomorphism.T d p f)

/-- H-1 with the predicted scalar `p^{d+1}` implies H-2. -/
theorem homologyPrintedSentence_of_bridge {p d : ℕ} [Fact p.Prime] (hd : Even d)
    (h : HomologyHomBridge p d ((p : ℚ) ^ (d + 1))) : HomologyPrintedSentence p d hd :=
  fun f => homology_printed_sentence_of_bridge h hd f

/-- Conversely, if the printed sentence holds for the homology operator on one `f` with `T_p f ≠ 0`, the
bridge scalar is `p^{d+1}`. -/
theorem bridge_scalar_of_printed_sentence {p d : ℕ} [Fact p.Prime] {c : ℚ}
    (h : HomologyHomBridge p d c) (hd : Even d) (f : Forms d)
    (hf : BinaryCuspHeckeEndomorphism.T d p f ≠ 0)
    (hs : homologyComplexT2 p d (periodMap d hd f) =
      periodMap d hd (BinaryCuspHeckeEndomorphism.T d p f)) :
    c = (p : ℚ) ^ (d + 1) := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hx : periodMap d hd (BinaryCuspHeckeEndomorphism.T d p f) ≠ 0 := fun hz =>
    hf (periodMap_injective' d hd (hz.trans (map_zero _).symm))
  rw [homology_periodMap_of_bridge h hd f] at hs
  have h2 : ((c : ℂ) * (p : ℂ) ^ (-((d : ℤ) + 1))) •
      periodMap d hd (BinaryCuspHeckeEndomorphism.T d p f) =
      (1 : ℂ) • periodMap d hd (BinaryCuspHeckeEndomorphism.T d p f) := by rw [hs, one_smul]
  have h3 := smul_left_injective ℂ hx h2
  have h4 : (c : ℂ) = (p : ℂ) ^ (d + 1) := by
    have e : (p : ℂ) ^ (-((d : ℤ) + 1)) = ((p : ℂ) ^ (d + 1))⁻¹ := by
      rw [zpow_neg]
      congr 1
    rw [e] at h3
    have hpd : (p : ℂ) ^ (d + 1) ≠ 0 := pow_ne_zero _ hp
    field_simp at h3
    exact h3
  exact_mod_cast h4

end TernaryPeriodPolynomials.Argument.HeckeNormalization
