import OddZetaSix.SixAnalyticCertCore

/-! Auto-generated analytic certificate shard 1: [7/32, 83/256] (15 cells). -/

set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix.AnalyticData

def shard1Cells : List AnalyticCell := [
  ⟨7 / 32, 29 / 128, true⟩,
  ⟨29 / 128, 59 / 256, true⟩,
  ⟨59 / 256, 15 / 64, true⟩,
  ⟨15 / 64, 31 / 128, true⟩,
  ⟨31 / 128, 1 / 4, true⟩,
  ⟨1 / 4, 33 / 128, true⟩,
  ⟨33 / 128, 17 / 64, true⟩,
  ⟨17 / 64, 35 / 128, true⟩,
  ⟨35 / 128, 9 / 32, true⟩,
  ⟨9 / 32, 19 / 64, true⟩,
  ⟨19 / 64, 39 / 128, true⟩,
  ⟨39 / 128, 5 / 16, true⟩,
  ⟨5 / 16, 81 / 256, true⟩,
  ⟨81 / 256, 41 / 128, true⟩,
  ⟨41 / 128, 83 / 256, true⟩
]

theorem shard1_ok : checkCellChain (7 / 32) (83 / 256) shard1Cells = true := by
  decide +kernel

end OddZetaSix.AnalyticData
