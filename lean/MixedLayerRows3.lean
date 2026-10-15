import MixedLayerRows2

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnMixedLayer

theorem recurrence_3 : nextList 9 row3.toList = row4.toList := by decide

end HeilbronnMixedLayer
