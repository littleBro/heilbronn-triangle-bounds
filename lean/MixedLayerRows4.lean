import MixedLayerRows3

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnMixedLayer

theorem recurrence_4 : nextList 9 row4.toList = row5.toList := by decide

end HeilbronnMixedLayer
