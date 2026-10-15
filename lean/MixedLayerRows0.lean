import MixedLayerCounting

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnMixedLayer

theorem recurrence_0 : nextList 9 row0.toList = row1.toList := by decide

end HeilbronnMixedLayer
