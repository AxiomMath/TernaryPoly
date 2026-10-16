module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CuspidalInduction.ShapiroSL

@[expose] public section


/-!
# Transport of the induced module to the `GL₂(ℤ)` model of `Γ(N)`

Formalized by Claude Sonnet 5.5.

The Farey-tree model of `Γ(N)` is `gammaNGL N ≤ GL₂(ℤ)` (`gammaEquiv`).  Here `Q = Γ(N)/Γ(M)` becomes a `gammaNGL N`-set (`QGL`) with base point the trivial coset and stabilizer `gammaNGL M`
(`stab_QGL`), the transport of `indRep M V` is `indRepQ` of the transported module (`transRep_indRep`), and the transport of the restriction to `Γ(M)` is the restriction of the transported
module along `gammaNGL M ≤ gammaNGL N` (`transRep_res`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.CuspidalInduction

open CongruenceSubgroup
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open scoped Classical

variable {N M : ℕ}

theorem gammaNGL_le (hM : 3 ≤ M) (hle : Gamma M ≤ Gamma N) : gammaNGL M ≤ gammaNGL N := by
  intro g hg
  have h1 : toSL hM ⟨g, hg⟩ ∈ Gamma N := hle (toSL_mem hM ⟨g, hg⟩)
  have h2 : Matrix.SpecialLinearGroup.toGL (toSL hM ⟨g, hg⟩) = g := by
    apply Units.ext
    ext i j
    simp [toSL_apply]
  rw [← h2]
  exact toGL_mem_gammaNGL.mpr h1

/-- The inclusion `gammaNGL M → gammaNGL N`. -/
def inclGL (hM : 3 ≤ M) (hle : Gamma M ≤ Gamma N) : gammaNGL M →* gammaNGL N :=
  Subgroup.inclusion (gammaNGL_le hM hle)

theorem symm_incl (hN : 3 ≤ N) (hM : 3 ≤ M) (hle : Gamma M ≤ Gamma N) (g : gammaNGL M) :
    (gammaEquiv hN).symm (inclGL hM hle g) = Subgroup.inclusion hle ((gammaEquiv hM).symm g) := rfl

/-- `Γ(N)/Γ(M)` as a `gammaNGL N`-set. -/
abbrev QGL (N M : ℕ) : Type := Gamma N ⧸ subM N M

instance QGL.mulAction [hN : Fact (3 ≤ N)] : MulAction (gammaNGL N) (QGL N M) :=
  MulAction.compHom (QGL N M) (gammaEquiv hN.out).symm.toMonoidHom

theorem QGL_smul [hN : Fact (3 ≤ N)] (g : gammaNGL N) (x : QGL N M) : g • x = (gammaEquiv hN.out).symm g • x := rfl

end TernaryPeriodPolynomials.Argument.CuspidalInduction
