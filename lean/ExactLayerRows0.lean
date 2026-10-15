import ExactLayerCounting

set_option maxRecDepth 4096

namespace HeilbronnExactLayer

theorem recurrence_0 : nextList row0.toList = row1.toList := by decide

theorem recurrence_1 : nextList row1.toList = row2.toList := by decide

theorem recurrence_2 : nextList row2.toList = row3.toList := by decide

end HeilbronnExactLayer
