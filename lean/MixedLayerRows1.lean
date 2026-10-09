import MixedLayerRows0

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnMixedLayer

theorem recurrence_3 : nextList 9 row3.toList = row4.toList := by decide

theorem recurrence_4 : nextList 9 row4.toList = row5.toList := by decide

theorem recurrence_5 : nextList 9 row5.toList = row6.toList := by decide

end HeilbronnMixedLayer
