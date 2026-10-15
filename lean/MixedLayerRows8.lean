import MixedLayerRows7

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnMixedLayer

theorem recurrence_8 : nextList 10 row8.toList = row9.toList := by decide

end HeilbronnMixedLayer
