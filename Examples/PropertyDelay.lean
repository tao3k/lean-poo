import LeanPoo.Functional.PropertyDelay

open LeanPoo.Functional.PropertyTesting

-- One remaining constructor can finish immediately, but zero cannot enter it.
example : restoredDelayed (fun _ : Nat => (Sum.inl 7 : Sum Nat Nat)) 1 (some 0) none 0 = (none, 0) := rfl
-- A two-stage constructor cannot acquire a second credit during regeneration.
example : restoredDelayed (fun state : Nat => if state = 0 then Sum.inr 1 else Sum.inl 7)
    2 (some 1) none 0 = (none, 1) := rfl
example : restoredDelayed (fun state : Nat => if state = 0 then Sum.inr 1 else Sum.inl 7)
    2 (some 2) none 0 = (some 7, 2) := rfl
-- A stricter consuming scope is retained by descendants after that scope exits.
example : delayMeet (delayMeet (some 3) (some 1)) none = some 1 := rfl
example : restoredDelayed (fun state : Nat => if state = 0 then Sum.inr 1 else Sum.inl 7)
    2 (delayMeet (some 3) (some 1)) none 0 = (none, 1) := rfl
-- Unbounded contexts preserve ordinary independent finite construction.
example : restoredDelayed (fun state : Nat => if state = 0 then Sum.inr 1 else Sum.inl 7)
    2 none none 0 = (some 7, 2) := rfl

-- A paused producer with three saved credits cannot force inside a zero-credit caller.
example : resumedDelayed (fun _ : Nat => (Sum.inl 0 : Sum Nat Nat))
    1 (some 3) (some 3) (some 0) 0 = (none, 0) := rfl
-- One incoming credit permits the same constructor, independently of prior suspension.
example : resumedDelayed (fun _ : Nat => (Sum.inl 0 : Sum Nat Nat))
    1 (some 3) none (some 1) 0 = (some 0, 1) := rfl
-- A two-stage constructor still cannot renew the incoming caller's single credit.
example : resumedDelayed (fun state : Nat => if state = 0 then Sum.inr 1 else Sum.inl 7)
    2 (some 3) (some 3) (some 1) 0 = (none, 1) := rfl

-- Map/filter/product scopes forward the current caller before restoring saved limits.
example : composedDelayed (fun _ : Nat => (Sum.inl 0 : Sum Nat Nat))
    1 (some 3) [none, some 4, some 3] (some 0) 0 = (none, 0) := rfl
-- One sufficient credit still permits the same branch through all sample layers.
example : composedDelayed (fun _ : Nat => (Sum.inl 0 : Sum Nat Nat))
    1 (some 3) [none, some 4, some 3] (some 1) 0 = (some 0, 1) := rfl
-- Grouping the same path into a product and a mapping cannot renew its allowance.
example : delayPathAllowance ([some 3, none] ++ [some 4]) (some 1) = some 1 := rfl
