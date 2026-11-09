/-! Planted controls for the decode step (DECODE-DESIGN.md, controls 3 and 5).  Pasted into the check file's body, so
everything here is the project's own. -/
namespace RefereeDecodeControls

/-- must fire:  addition on the naturals written out by recursion;  `Nat.add` must be in the top 10. -/
def addOut : Nat → Nat → Nat
  | n, 0 => n
  | n, m + 1 => Nat.succ (addOut n m)

/-- the planted inductive, found only here. -/
inductive Trit where
  | lo | mid | hi

/-- planted absence:  built on `Trit` alone;  must have no candidate. -/
def tritonicHyperbracket : Trit → Trit → Trit
  | .lo, t => t
  | .mid, .lo => .hi
  | .mid, t => t
  | .hi, _ => .lo

/-- planted absence:  built on `Trit` alone;  must have no candidate. -/
def tritonicTwist : Trit → Trit
  | .lo => .mid
  | .mid => .hi
  | .hi => .lo

end RefereeDecodeControls
