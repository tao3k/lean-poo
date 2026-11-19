-- SPDX-License-Identifier: Apache-2.0 AND LGPL-2.1-or-later
import Std

namespace LeanPoo.Object.CompactPrototypeMap

/-- The array is the initialized prefix of a private vector. Each accepted
entry is written at the prefix length. A rejection publishes no vector. -/
def captureInto (capture : Input → Except Failure Row) :
    Array Row → List Input → Except Failure (Array Row)
  | filled, [] => .ok filled
  | filled, entry :: rest => do
    let row ← capture entry
    captureInto capture (filled.push row) rest

/-- The old map-then-convert and the direct fill perform the same captures,
left to right. Representatives and repeated keys keep their original order. -/
theorem captures_in_order (capture : Input → Except Failure Row) (source : List Input)
    (filled : Array Row) :
    (captureInto capture filled source).map Array.toList =
      (source.mapM capture).map (fun rows => filled.toList ++ rows) := by
  induction source generalizing filled with
  | nil => simp [captureInto, Except.map, pure, Except.pure]
  | cons entry rest ih =>
    cases next : capture entry with
    | error cause => simp [captureInto, List.mapM_cons, next, Except.map, bind, Except.bind]
    | ok row =>
      simp only [captureInto, List.mapM_cons, next, Except.bind, bind, Except.map] at *
      rw [ih]
      cases rest.mapM capture <;> simp [pure, Except.pure, List.append_assoc]

/-- Exactly one admitted entry consumes each position of the destination,
so the complete input length is sufficient capacity. -/
theorem capture_count (capture : Input → Except Failure Row) (source : List Input)
    (filled output : Array Row) (captured : captureInto capture filled source = .ok output) :
    output.size = filled.size + source.length := by
  induction source generalizing filled with
  | nil => cases captured; simp
  | cons entry rest ih =>
    cases next : capture entry with
    | error cause => simp [captureInto, next, Except.bind, bind] at captured
    | ok row =>
      have restCaptured : captureInto capture (filled.push row) rest = .ok output := by
        simpa [captureInto, next, Except.bind, bind] using captured
      rw [ih (filled.push row) restCaptured, Array.size_push, List.length_cons]
      omega

end LeanPoo.Object.CompactPrototypeMap
