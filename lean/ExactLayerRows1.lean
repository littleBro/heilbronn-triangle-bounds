import ExactLayerCounting

set_option maxRecDepth 4096

namespace HeilbronnExactLayer

theorem recurrence_3 : nextList row3.toList = row4.toList := by decide

theorem recurrence_4 : nextList row4.toList = row5.toList := by decide

theorem recurrence_5 : nextList row5.toList = row6.toList := by decide

end HeilbronnExactLayer
