import MixedLayerRows1

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnMixedLayer

theorem recurrence_6 : nextList 9 row6.toList = row7.toList := by decide

theorem recurrence_7 : nextList 9 row7.toList = row8.toList := by decide

theorem recurrence_8 : nextList 10 row8.toList = row9.toList := by decide

end HeilbronnMixedLayer
