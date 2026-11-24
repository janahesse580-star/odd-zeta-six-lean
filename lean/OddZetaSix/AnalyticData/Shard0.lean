import OddZetaSix.SixAnalyticCertCore

/-! Auto-generated analytic certificate shard 0: [0, 7/32] (15 cells). -/

set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix.AnalyticData

def shard0Cells : List AnalyticCell := [
  ⟨0, 1 / 16, false⟩,
  ⟨1 / 16, 5 / 64, false⟩,
  ⟨5 / 64, 11 / 128, false⟩,
  ⟨11 / 128, 3 / 32, false⟩,
  ⟨3 / 32, 13 / 128, false⟩,
  ⟨13 / 128, 7 / 64, false⟩,
  ⟨7 / 64, 1 / 8, false⟩,
  ⟨1 / 8, 9 / 64, false⟩,
  ⟨9 / 64, 5 / 32, false⟩,
  ⟨5 / 32, 11 / 64, false⟩,
  ⟨11 / 64, 3 / 16, true⟩,
  ⟨3 / 16, 25 / 128, true⟩,
  ⟨25 / 128, 13 / 64, true⟩,
  ⟨13 / 64, 27 / 128, true⟩,
  ⟨27 / 128, 7 / 32, true⟩
]

theorem shard0_ok : checkCellChain (0) (7 / 32) shard0Cells = true := by
  decide +kernel

end OddZetaSix.AnalyticData
