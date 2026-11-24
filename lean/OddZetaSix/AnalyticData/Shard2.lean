import OddZetaSix.SixAnalyticCertCore

/-! Auto-generated analytic certificate shard 2: [83/256, 103/256] (15 cells). -/

set_option autoImplicit false
set_option Elab.async false

namespace OddZetaSix.AnalyticData

def shard2Cells : List AnalyticCell := [
  ⟨83 / 256, 21 / 64, true⟩,
  ⟨21 / 64, 43 / 128, true⟩,
  ⟨43 / 128, 11 / 32, true⟩,
  ⟨11 / 32, 45 / 128, true⟩,
  ⟨45 / 128, 91 / 256, true⟩,
  ⟨91 / 256, 23 / 64, true⟩,
  ⟨23 / 64, 93 / 256, true⟩,
  ⟨93 / 256, 47 / 128, true⟩,
  ⟨47 / 128, 95 / 256, true⟩,
  ⟨95 / 256, 3 / 8, true⟩,
  ⟨3 / 8, 49 / 128, true⟩,
  ⟨49 / 128, 25 / 64, true⟩,
  ⟨25 / 64, 101 / 256, true⟩,
  ⟨101 / 256, 51 / 128, true⟩,
  ⟨51 / 128, 103 / 256, true⟩
]

theorem shard2_ok : checkCellChain (83 / 256) (103 / 256) shard2Cells = true := by
  decide +kernel

end OddZetaSix.AnalyticData
