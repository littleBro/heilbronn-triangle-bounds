import MixedLayerRows4

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnMixedLayer

theorem recurrence_5 : nextList 9 row5.toList = row6.toList := by decide

end HeilbronnMixedLayer
