import PairedLayerCounting

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace HeilbronnPairedLayer

theorem recurrence_0 : nextList 6 row0.toList = row1.toList := by decide

theorem recurrence_1 : nextList 6 row1.toList = row2.toList := by decide

theorem recurrence_2 : nextList 6 row2.toList = row3.toList := by decide

theorem recurrence_3 : nextList 6 row3.toList = row4.toList := by decide

theorem recurrence_4 : nextList 6 row4.toList = row5.toList := by decide

end HeilbronnPairedLayer
