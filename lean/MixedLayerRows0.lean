import MixedLayerCounting

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnMixedLayer

theorem recurrence_0 : nextList 9 row0.toList = row1.toList := by decide

theorem recurrence_1 : nextList 9 row1.toList = row2.toList := by decide

theorem recurrence_2 : nextList 9 row2.toList = row3.toList := by decide

end HeilbronnMixedLayer
