import LeanPoo.Prototype.GeneralizedDependencies

/-! Reusable future-work client: a tariff component with existing standard
method combination and a two-step kernel closure witness. -/
namespace LeanPoo.Prototype.Generalized.TariffComponent
open Object.MethodCombination
abbrev Action := EStateM String (List String)
abbrev Methods := Object.MethodCombination.Methods Int Action Int
structure Account where
  rate : Int
  methods : Methods := {}
structure Local where
  rate : Int
  price : Int → Action Int
abbrev Method := Thunk Int → Contribution Int Action Int
abbrev Fragment := Sum Int Method

def rateFocus : MonoLens Account Int := MonoLens.ofGetSet (·.rate) (fun value raw => {raw with rate := value})
def methodsFocus : MonoLens Account Methods := MonoLens.ofGetSet (·.methods) (fun value raw => {raw with methods := value})
def narrow (dependency : Int) : Protocol Account Int Fragment :=
  ⟨Account.rate,sumCompiler (lensCompiler rateFocus (fun rate _ _ => rate+dependency)) (standardCompiler methodsFocus)⟩
def localCook (raw : Account) : Local := ⟨raw.rate,effective raw.methods (fun _ => throw "missing")⟩
def family (dependency : Int) : Protocol Account Local Fragment := (narrow dependency).reindexSelf Local.rate localCook
abbrev upstreamProtocol := family 0

theorem family_step (dependency : Int) (fragments : List Fragment) :
    (family dependency).step fragments = (narrow dependency).step fragments :=
  (narrow dependency).step_reindexSelf Local.rate localCook (fun _ => rfl) fragments

theorem rate_stable (dependency rate : Int) (rest : List Fragment) (base : Account) :
    (family dependency).approximate (.inl rate :: rest) base base 3 =
      (family dependency).approximate (.inl rate :: rest) base base 2 := by
  simp only [Protocol.approximate,family_step]
  exact (narrow dependency).stable_two _ base base (rate+dependency) (fun _ => rfl)

def closeLocal (dependency : Int) (fragments : List Fragment) (base : Account) :
    Except String (Closed (family dependency) fragments base) :=
  match fragments with
  | .inl rate :: rest => .ok ((family dependency).closeAt (.inl rate :: rest) base base 2 (rate_stable dependency rate rest base))
  | _ => .error "leading rate witness required"

def mark (event : String) : Action Unit := modify (· ++ [event])

def stageFragments (rate : Int) (name : String) (limit : Option Int := none) : List Fragment := [
  .inl rate,
  .inr (fun _ => .around (fun next units => do
    mark (name ++ ".enter")
    if units < 0 then throw "units"
    match limit with
    | some bound => if units > bound then throw (name ++ ".limit")
    | none => pure ()
    let result ← next ()
    mark (name ++ ".exit")
    return result)),
  .inr (fun self => .primary (fun _ units => do mark name; return units * self.get))]


def summary : EStateM.Result String (List String) Int → Option Int × Option String × List String
  | .ok value state => (some value,none,state)
  | .error error state => (none,some error,state)

end LeanPoo.Prototype.Generalized.TariffComponent
