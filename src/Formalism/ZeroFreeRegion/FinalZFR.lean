module

public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivBound
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZeroFactor
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LandauLocalOf
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ThreeFourOne
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.LogDerivRight
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaGrowth
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZetaInvBound
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.SmallHeight
public import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.ZeroFreeOf
public import Formalism.ZeroFreeRegion.SingleFile

@[expose] public section

noncomputable section

namespace Formalism.ZF

theorem landauLocal : LandauLocal := localZeroExpansionOfFactorization zeroFactorization logDerivBoundOnBall

theorem zeroFreeRegion : ZeroFreeRegion := zeroFreeRegion_compressed

end Formalism.ZF

