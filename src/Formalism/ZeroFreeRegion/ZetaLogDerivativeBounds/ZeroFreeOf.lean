import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZfoNegReLeNorm

namespace Formalism.ZF

/-- Glue the bounded-height strip to the logarithmic region at large heights. -/
theorem classicalZeroFreeRegionOfBounds : ZeroFreeOf := by
  intro h341 hright hgrowth hinv hsmall hlocal
  obtain ⟨T, _, hlarge⟩ := zfo_large h341 hright hgrowth hinv hlocal
  obtain ⟨δ, hδ, hstrip⟩ := hsmall T
  have h₂ : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min (1 / 200000) (δ * Real.log 2), lt_min (by norm_num) (mul_pos hδ h₂), ?_⟩
  intro s hs hσ hzero
  have hlog : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg s.im])
  rcases le_total |s.im| T with ht | ht
  · apply hstrip s ht _ hs hzero
    have hwidth := (div_le_iff₀ (h₂.trans_le hlog)).2 <|
      (min_le_right (1 / 200000) _).trans (mul_le_mul_of_nonneg_left hlog hδ.le)
    linarith
  · have hβ := hlarge s.re s.im ht (by simpa only [Complex.re_add_im] using hzero)
    have hwidth := div_le_div_of_nonneg_right (min_le_left (1 / 200000) (δ * Real.log 2))
      (h₂.trans_le hlog).le
    linarith

end Formalism.ZF
