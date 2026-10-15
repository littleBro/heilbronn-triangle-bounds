import MixedLayerRows1

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnMixedLayer

theorem recurrence_2 : nextList 9 row2.toList = row3.toList := by decide

end HeilbronnMixedLayer
