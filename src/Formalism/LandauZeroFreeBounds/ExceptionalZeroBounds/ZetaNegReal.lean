import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.MellinRemainder

open Complex Formalism.ZF.MellinRemainder

namespace Formalism.ZeroFreeDirichlet

theorem zeta_negative_real_axis : ZetaNegReal := by
  intro σ hσ hσ1
  obtain ⟨r, hr, he⟩ := remainder_ofReal σ
  have hn : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1.ne
  have hζ : riemannZeta (σ : ℂ) = ((σ / (σ - 1) - σ * r : ℝ) : ℂ) := by
    rw [riemannZeta_eq_inv_sub_add hn, regular_eq (by simpa using hσ), he]
    push_cast
    field_simp
    ring
  rw [hζ, ofReal_im, ofReal_re]
  exact ⟨rfl, sub_lt_zero.mpr ((div_neg_of_pos_of_neg hσ (sub_neg.mpr hσ1)).trans_le
    (mul_nonneg hσ.le hr))⟩

end Formalism.ZeroFreeDirichlet
