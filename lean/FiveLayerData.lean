import Lean

namespace HeilbronnFiveLayer

def row0 : Array Nat := #[1, 0, 0]

def row1 : Array Nat := #[2, 0, 0]

def row2 : Array Nat := #[4, 0, 0]

def row3 : Array Nat := #[8, 0, 0]

def row4 : Array Nat := #[16, 0, 0]

def row5 : Array Nat := #[32, 0, 0]

def row6 : Array Nat := #[64, 64, 0]

def row7 : Array Nat := #[128, 256, 128]

def row8 : Array Nat := #[256, 768, 768]

def row9 : Array Nat := #[512, 2048, 3072]

end HeilbronnFiveLayer
