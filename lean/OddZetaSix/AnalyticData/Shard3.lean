import OddZetaSix.SixAnalyticCertCore

/-! Auto-generated analytic certificate shard 3: [103/256, 2] (13 cells). -/

set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix.AnalyticData

def shard3Cells : List AnalyticCell := [
  ⟨103 / 256, 13 / 32, true⟩,
  ⟨13 / 32, 53 / 128, true⟩,
  ⟨53 / 128, 27 / 64, true⟩,
  ⟨27 / 64, 55 / 128, true⟩,
  ⟨55 / 128, 7 / 16, true⟩,
  ⟨7 / 16, 29 / 64, true⟩,
  ⟨29 / 64, 15 / 32, true⟩,
  ⟨15 / 32, 1 / 2, true⟩,
  ⟨1 / 2, 9 / 16, true⟩,
  ⟨9 / 16, 5 / 8, true⟩,
  ⟨5 / 8, 3 / 4, true⟩,
  ⟨3 / 4, 1, true⟩,
  ⟨1, 2, true⟩
]

theorem shard3_ok : checkCellChain (103 / 256) (2) shard3Cells = true := by
  decide +kernel

end OddZetaSix.AnalyticData
