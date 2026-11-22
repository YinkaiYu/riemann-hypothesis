import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.MellinRemainder

open Formalism.ZF.MellinRemainder

namespace Formalism.ZF

theorem growthBound : ZetaGrowth := by
  intro s hs hs1
  rw [riemannZeta_eq_inv_sub_add hs1, regular_eq hs]
  grw [norm_add_le, norm_inv, norm_sub_le, norm_mul, remainder_bound hs]
  simp only [norm_one, one_div]
  nlinarith [norm_nonneg s]

end Formalism.ZF
