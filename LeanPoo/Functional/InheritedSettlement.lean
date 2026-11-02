import LeanPoo.Functional.InheritedMOP
import LeanPoo.Functional.ConstructionWorkflow

/-! An inherited settlement service joins C3 diamonds, analyzed super wrappers,
conditional overrides and exact-source protected publication. Future work. -/
namespace LeanPoo.Functional.InheritedSettlement
open GeneralizedGraph GeneralizedFragments
open ConstructionWorkflow (Values Raw Node Policy Config Call Action Method model watches keys Approval)

inductive Hazard where
  | source
  | opaque
  | cycle
  deriving Repr, BEq, DecidableEq

structure Settings where
  data : Config
  scale : Int := 2
  surcharge : Int := 3
  swapped : Bool := false
  conditional : Bool := false
  overrideInvoice : Option Int := none
  baseInvoice : Bool := true
  hazard : Hazard := .opaque
  forbidden : Bool := false
  deriving Repr

def graph (swapped : Bool) : Prototype.C3.Graph :=
  [("Service",if swapped then ["Scale","Regional"] else ["Regional","Scale"]),
    ("Regional",["Base"]),("Scale",["Base"]),("Base",["Legacy"]),("Legacy",[])]

def legacy (hazard : Hazard) : Node "invoice" :=
  match hazard with
  | .source => .failure "legacy"
  | .opaque => .opaque fun _ _ => .ok (.ok 999)
  | .cycle => ConstructionWorkflow.need "total" id

def core (settings : Settings) : List (Binding String Values) :=
  keys.filterMap fun key =>
    if key == "invoice" && !settings.baseInvoice then none
    else (ConstructionWorkflow.codes settings.data key).map fun code => ⟨key,.replace code⟩

/-- The modifier reads the final shared risk component, not inherited storage. -/
def addRisk : Modifier String Values "total" :=
  .need "risk" fun _ risk inherited => do return (← inherited) + (← risk)

def declarations (settings : Settings) (name : String) : List (Binding String Values) :=
  if name == "Service" then
    [⟨"total",.extend addRisk⟩] ++
    (match settings.overrideInvoice with
    | some value => [⟨"invoice",.replace (.pure fun _ => .ok value)⟩]
    | none => if settings.conditional then [⟨"invoice",.conditional
        (.inspect "discount" fun _ present => present)
        (ConstructionWorkflow.need "settlement" (· + 100))⟩] else []) ++
    (if settings.forbidden then [⟨"permit",.replace (.pure fun _ => .ok 1)⟩] else [])
  else if name == "Regional" then [⟨"invoice",.extend
    (.pure fun _ inherited => inherited.map (· + settings.surcharge))⟩]
  else if name == "Scale" then [⟨"invoice",.extend
    (.pure fun _ inherited => inherited.map (· * settings.scale))⟩]
  else if name == "Base" then core settings
  else if name == "Legacy" then [⟨"invoice",.replace (legacy settings.hazard)⟩]
  else []

def source (settings : Settings) (policy : Policy) : InheritedMOP.Source String Values Policy :=
  ⟨graph settings.swapped,"Service",declarations settings,keys,(ConstructionWorkflow.graph settings.data).base,policy⟩

abbrev Version := InheritedMOP.Snapshot model watches Approval

def start (settings : Settings) (policy : Policy) (limit : Int) :=
  (InheritedMOP.stage model watches (source settings policy) (ConstructionWorkflow.admit limit)).map
    fun revision => revision.snapshot

def migrate (old : Version) (settings : Settings) (policy : Policy) (limit : Int) :=
  InheritedMOP.publish model watches old (source settings policy) (ConstructionWorkflow.admit limit)

def failureTag : InheritedMOP.Failure (AdmissionError := String) model watches → String
  | .inheritance error => "inheritance:" ++ reprStr error
  | .construction error => ConstructionWorkflow.publicationTag error

/-- At the class-local replace boundary, arbitrary legacy footprints disappear.
This concerns all possible final selves, not just the current data snapshot. -/
theorem core_override_prunes (settings : Settings) (parents : List (Fragment String Values "invoice"))
    (base : Option (Outcome String Values "invoice")) :
    compile "invoice" base (.replace (ConstructionWorkflow.need "settlement" (· + settings.data.invoiceFee)) :: parents) =
      ConstructionWorkflow.need "settlement" (· + settings.data.invoiceFee) := rfl

/-- The actual compiled inherited computation has the declared noncommuting
order, for every final provider and successful inherited source computation. -/
theorem invoice_wrappers (scale surcharge value : Int) (code : Node "invoice")
    (provider : Provider Unit String (fun _ dep => Outcome String Values dep))
    (succeeded : code.evaluate provider () = .ok (.ok value)) :
    (compile "invoice" none [
      .extend (.pure fun _ inherited => inherited.map (· + surcharge)),
      .extend (.pure fun _ inherited => inherited.map (· * scale)),.replace code]).evaluate provider () =
        .ok (.ok (value * scale + surcharge)) := by
  simp [compile, Computation.evaluate, succeeded, bind, Except.bind, Except.map, pure, Except.pure]

/-- Noncommuting source order has a directly observable arithmetic distinction. -/
theorem order_difference (value scale surcharge : Int) :
    ((value + surcharge) * scale) - (value * scale + surcharge) = surcharge * (scale - 1) := by
  simp only [Int.add_mul, Int.mul_sub, Int.mul_one]
  omega

end LeanPoo.Functional.InheritedSettlement
