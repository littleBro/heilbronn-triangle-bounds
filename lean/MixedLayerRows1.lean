import MixedLayerRows0

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnMixedLayer

theorem recurrence_1 : nextList 9 row1.toList = row2.toList := by decide

end HeilbronnMixedLayer
