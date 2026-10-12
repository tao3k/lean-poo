import LeanPoo.Functional.DependencyAnalysis

namespace LeanPoo.Tests.FunctionalDependencyAnalysis
open Functional
universe u v w
example {Context : Type u} {Key : Type v} {Value : Context → Key → Type w}
    {Result : Context → Type w} (code : Computation Context Key Value Result)
    (left right : Provider Context Key Value) (known : code.analyze.unknown = false)
    (values : ∀ key ∈ code.analyze.values, left key = right key)
    (presences : ∀ key ∈ code.analyze.presences, (left key).isSome = (right key).isSome) (c : Context) :
    code.evaluate left c = code.evaluate right c := code.evaluate_congr left right known values presences c

private inductive Key where
  | quantity | flag | proof | ghost | trap
  deriving BEq, DecidableEq, Repr
private def Value (c : Nat) : Key → Type
  | .quantity => {n : Nat // c ≤ n}
  | .flag => Bool
  | .proof => PLift (c ≤ c + 1)
  | .ghost | .trap => Nat
private partial def neverFinish (c : Nat) : Nat := neverFinish c
private def present (mask : Nat) (key : Key) : Bool :=
  mask / (match key with | .quantity => 1 | .flag => 2 | .proof => 4 | .ghost => 8 | .trap => 16) % 2 == 1
private def provider (mask version : Nat) : Provider Nat Key Value := fun key =>
  if present mask key then some (match key with
    | .quantity => fun c => ⟨c + version + 1, by omega⟩
    | .flag => fun c => (c+version) % 2 == 0
    | .proof => Factory.fromProof (fun _ => by omega)
    | .ghost => fun c => c+version+10
    | .trap => neverFinish) else none
private abbrev Code := Computation Nat Key Value (fun _ => Nat)
private def codes : List Code :=
  [.pure (fun c => c+1),
   .need .quantity (fun _ q => q.val),
   .read .flag (fun _ value => match value with | none => 7 | some true => 1 | some false => 0),
   .inspect .ghost (fun _ b => if b then 5 else 11),
   .deny .ghost (fun c => c+3),
   .both (.map (.need .quantity (fun _ q => q.val)) (fun _ n => n+2))
     (.need .proof (fun _ _ => 1)) (fun _ q p => q+p),
   .choose (.need .flag (fun _ b => b)) (fun _ b => b)
     (.need .quantity (fun _ q => q.val)) (.read .ghost (fun _ n => (show Option Nat from n).getD 42)),
   .both (show Code from .failure "stop") (.need .trap (fun _ n => n)) (fun _ _ n => n),
   .inspect .trap (fun _ b => if b then 1 else 0),
   .choose (.pure (fun _ => false)) (fun _ b => b) (.need .trap (fun _ n => n)) (.pure (fun _ => 0)),
   .opaque (fun view c => .ok ((Functional.apply view c .quantity).map Subtype.val |>.getD 99)),
   .both (.need .quantity (fun _ q => q.val)) (.deny .ghost (fun _ => 1)) (fun _ q n => q+n)]
private def oracle (id mask version c : Nat) : Except (ComputationError Key) Nat :=
  match id with
  | 0 => .ok (c+1)
  | 1 => if present mask .quantity then .ok (c+version+1) else .error (.missing .quantity)
  | 2 => .ok (if present mask .flag then if (c+version)%2==0 then 1 else 0 else 7)
  | 3 => .ok (if present mask .ghost then 5 else 11)
  | 4 => if present mask .ghost then .error (.introduced .ghost) else .ok (c+3)
  | 5 => if !(present mask .quantity) then .error (.missing .quantity)
      else if !(present mask .proof) then .error (.missing .proof) else .ok (c+version+4)
  | 6 => if !(present mask .flag) then .error (.missing .flag)
      else if (c+version)%2==0 then
        if present mask .quantity then .ok (c+version+1) else .error (.missing .quantity)
      else .ok (if present mask .ghost then c+version+10 else 42)
  | 7 => .error (.source "stop")
  | 8 => .ok (if present mask .trap then 1 else 0)
  | 9 => .ok 0
  | 10 => .ok (if present mask .quantity then c+version+1 else 99)
  | _ => if !(present mask .quantity) then .error (.missing .quantity)
      else if present mask .ghost then .error (.introduced .ghost) else .ok (c+version+2)
private def footprints : List (List Key × List Key × List Key × List Key × Bool) :=
  [([],[],[],[],false), ([.quantity],[],[.quantity],[],false), ([.flag],[],[],[],false),
   ([],[.ghost],[],[],false), ([],[.ghost],[],[.ghost],false),
   ([.quantity,.proof],[],[.quantity,.proof],[],false),
   ([.flag,.quantity,.ghost],[],[.flag,.quantity],[],false),
   ([.trap],[],[.trap],[],false), ([],[.trap],[],[],false),
   ([.trap],[],[.trap],[],false), ([],[],[],[],true),
   ([.quantity],[.ghost],[.quantity],[.ghost],false)]

private def same : Except (ComputationError Key) Nat → Except (ComputationError Key) Nat → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

#eval do
  IO.println "FUNCTIONAL-DEPENDENCY-ANALYSIS-START"
  let mut cases := 0
  let mut stable := 0
  for (code, id) in codes.zipIdx do
    let some (values, presences, required, forbidden, unknown) := footprints[id]? |
      throw (IO.userError "missing footprint control")
    let report := code.analyze
    unless report.values == values && report.presences == presences && report.required == required &&
        report.forbidden == forbidden && report.unknown == unknown do
      throw (IO.userError s!"hidden/nested/branch footprint incorrect: {id}")
    for mask in List.range 32 do
      for version in [0, 3] do
        for c in [0, 7] do
          unless same (code.evaluate (provider mask version) c) (oracle id mask version c) do
            throw (IO.userError s!"computation differs from scalar control: {id}")
          cases := cases+1
      for nextMask in List.range 32 do
        for nextVersion in [0, 3] do
          let unchanged := !unknown && values.all (fun (key : Key) =>
            present mask key == present nextMask key &&
              (!(present mask key) || key == Key.proof || key == Key.trap || nextVersion == 0)) &&
            presences.all (fun key => present mask key == present nextMask key)
          if unchanged then
            for c in [0,7] do
              unless same (code.evaluate (provider mask 0) c) (code.evaluate (provider nextMask nextVersion) c) do
                throw (IO.userError "known footprint missed a dependency")
            stable := stable+1
  unless cases == 1536 && stable == 9616 do throw (IO.userError "analysis coverage changed")
  IO.println s!"FUNCTIONAL-DEPENDENCY-ANALYSIS-OK observations={cases} stable={stable}"

#print axioms LeanPoo.Functional.Computation.evaluate_congr
#print axioms LeanPoo.Functional.Computation.evaluate_capabilitySafe
end LeanPoo.Tests.FunctionalDependencyAnalysis
