universe u v

inductive BExp (T : Type v) : Type v
  | zero : BExp T
  | one : BExp T
  | prim : T → BExp T
  | and : BExp T → BExp T → BExp T
  | or : BExp T → BExp T → BExp T
  | not : BExp T → BExp T
deriving Repr

inductive Exp (σ : Type u) (T : Type v) : Type (max u v)
  | do : σ → Exp σ T
  | assert : BExp T → Exp σ T
  | seq : Exp σ T → Exp σ T → Exp σ T
  | if : BExp T → Exp σ T → Exp σ T → Exp σ T
  | while : BExp T → Exp σ T → Exp σ T
deriving Repr
