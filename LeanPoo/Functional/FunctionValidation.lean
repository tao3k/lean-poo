import LeanPoo.Functional.ObjectContract

/-! Function descriptor validation interpreted with pure, terminating callbacks.
Arguments/results may be products, rows or functions; the host Function protocol
owns their arity/representation. These laws do not certify a Scheme runtime. -/
namespace LeanPoo.Functional.FunctionValidation

/-- Validate arguments before the source, then validate its returned value. An
output validator may itself wrap a higher-order result. Reuse checkedAction. -/
def wrap (input : Args → Except Error CheckedArgs)
    (output : RawResult → Except Error Result)
    (source : CheckedArgs → Except Error RawResult) (args : Args) : Except Error Result :=
  ObjectContract.checkedAction input (fun checked => (source checked).bind output) args

/-- Input refusal suppresses source/output evaluation in this pure interpretation. -/
theorem input_error (input : Args → Except Error CheckedArgs) (output : RawResult → Except Error Result)
    (source : CheckedArgs → Except Error RawResult) (args : Args) (error : Error)
    (failed : input args = .error error) : wrap input output source args = .error error := by
  simp [wrap, ObjectContract.checkedAction, failed, Except.bind]

/-- A source error is retained exactly after argument validation. -/
theorem source_error (input : Args → Except Error CheckedArgs) (output : RawResult → Except Error Result)
    (source : CheckedArgs → Except Error RawResult) (args : Args) (checked : CheckedArgs) (error : Error)
    (accepted : input args = .ok checked) (failed : source checked = .error error) :
    wrap input output source args = .error error := by
  simp [wrap, ObjectContract.checkedAction, accepted, failed, Except.bind]

/-- Both normalizations are passed through; multiple values can be modeled by a
product, and higher-order output by a function carrier without decidable equality. -/
theorem returned (input : Args → Except Error CheckedArgs) (output : RawResult → Except Error Result)
    (source : CheckedArgs → Except Error RawResult) (args : Args) (checked : CheckedArgs) (raw : RawResult)
    (accepted : input args = .ok checked) (called : source checked = .ok raw) :
    wrap input output source args = output raw := by
  simp [wrap, ObjectContract.checkedAction, accepted, called, Except.bind]

/-- A successful wrapper result has passed the supplied output validator. -/
theorem success (input : Args → Except Error CheckedArgs) (output : RawResult → Except Error Result)
    (source : CheckedArgs → Except Error RawResult) (args : Args) (result : Result) :
    wrap input output source args = .ok result ↔
      ∃ checked raw, input args = .ok checked ∧ source checked = .ok raw ∧ output raw = .ok result := by
  cases hi : input args <;> simp [wrap, ObjectContract.checkedAction, hi, Except.bind]
  case ok checked => cases source checked <;> simp
end LeanPoo.Functional.FunctionValidation
