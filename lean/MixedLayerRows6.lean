import MixedLayerRows5

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnMixedLayer

theorem recurrence_6 : nextList 9 row6.toList = row7.toList := by decide

end HeilbronnMixedLayer
