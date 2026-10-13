import Lean

namespace HeilbronnSevenLayer

def row0 : Array Nat := #[1, 0, 0, 0, 0, 0]

def row1 : Array Nat := #[2, 2, 0, 0, 0, 0]

def row2 : Array Nat := #[4, 8, 4, 0, 0, 0]

def row3 : Array Nat := #[8, 24, 24, 8, 0, 0]

def row4 : Array Nat := #[16, 64, 96, 64, 16, 0]

def row5 : Array Nat := #[32, 160, 320, 320, 160, 32]

def row6 : Array Nat := #[64, 384, 960, 1280, 960, 384]

def row7 : Array Nat := #[128, 896, 2688, 4480, 4480, 2688]

def row8 : Array Nat := #[256, 2048, 7168, 14336, 17920, 14336]

def row9 : Array Nat := #[512, 4608, 18432, 43520, 68608, 78848]

end HeilbronnSevenLayer
