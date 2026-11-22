import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LandauLocalOf
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivBound
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ThreeFourOne
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZeroFactor
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZeroFreeOf

namespace Formalism.ZF

/-- Restrict the logarithmic zero-free region to a bounded interval of heights. -/
theorem zeroFreeBoundedHeight : SmallHeight := by
  intro T
  obtain ⟨c, hc, hregion⟩ := ClassicalZeroFreeProof.from_local_zero_expansion
    (localZeroExpansionOfFactorization zeroFactorization logDerivBoundOnBall) mertensInequality
  have hlog (u : ℝ) : 0 < Real.log (|u| + 2) :=
    Real.log_pos (by linarith [abs_nonneg u])
  refine ⟨c / Real.log (|T| + 2), div_pos hc (hlog T), fun s hs hre hs₁ => hregion s hs₁ ?_⟩
  have hmon : Real.log (|s.im| + 2) ≤ Real.log (|T| + 2) :=
    Real.log_le_log (by linarith [abs_nonneg s.im]) (by linarith [le_abs_self T])
  linarith [div_le_div_of_nonneg_left hc.le (hlog s.im) hmon]

end Formalism.ZF
