import Lean
import LeanPoo.Prototype.DictionaryBridge

/-! Generate a typed dependent field representation and kernel-checked inverse
conversions directly from a Lean structure/class constructor. Inherited
subobjects, functions, type fields and dependent proof fields are retained. -/
namespace LeanPoo.Deriving
open Lean Meta Elab Command

private def generatedNames (destination : Name) : List Name :=
  ["Fields", "toFields", "fromFields", "from_toFields", "to_fromFields", "dictionaryBridge", "fieldNames", "fieldCount"].map
    (destination.str ·)

private def addDefinition (name : Name) (levels : List Name) (value : Expr) : MetaM Unit := do
  let value ← instantiateMVars value
  let type ← inferType value
  addAndCompile <| .defnDecl {
    name := name
    levelParams := levels
    type := type
    value := value
    hints := .abbrev
    safety := .safe }
  setReducibilityStatus name .reducible

private def addInverse (name : Name) (levels : List Name) (params : Array Expr)
    (domain : Expr) (left : Expr → MetaM Expr) : MetaM Unit := do
  withLocalDeclD `value domain fun value => do
    let type ← mkForallFVars (params.push value) (← mkEq (← left value) value)
    let proof ← mkLambdaFVars (params.push value) (← mkEqRefl value)
    -- The kernel checks the actual generated functions, including dependent eta.
    addAndCompile <| .thmDecl { name := name, levelParams := levels, type := type, value := proof }

private def packFields (type : Expr) (values : Array Expr) : MetaM Expr := do
  let mut types := #[type]
  let mut current := type
  for value in values do
    unless current.isAppOfArity ``PSigma 2 do throwError "internal dependent field packing error"
    current := current.appArg!.bindingBody!.instantiate1 value
    types := types.push current
  let mut packed := mkConst ``PUnit.unit [.zero]
  for i in (List.range values.size).reverse do
    let type := types[i]!
    packed := mkApp4 (mkConst ``PSigma.mk type.getAppFn.constLevels!)
      type.appFn!.appArg! type.appArg! values[i]! packed
  return packed

private def generateDictionary (name destination : Name) : MetaM Unit := do
  let env ← getEnv
  unless isStructure env name do
    throwError "derive_dictionary expects a Type-valued structure or class: {name}"
  let ind ← getConstInfoInduct name
  unless ind.numIndices == 0 && ind.ctors.length == 1 do
    throwError "derive_dictionary requires a structure without indices: {name}"
  for generated in generatedNames destination do
    if env.contains generated then throwError "derive_dictionary declaration already exists: {generated}"
  let ctor ← getConstInfoCtor ind.ctors.head!
  let levels := ind.levelParams.map Level.param
  forallTelescopeReducing ctor.type fun arguments dictionaryType => do
    if ← isProp dictionaryType then
      throwError "derive_dictionary cannot make a runtime descriptor from a Prop-valued class: {name}"
    let params := arguments.extract 0 ind.numParams
    let fields := arguments.extract ind.numParams arguments.size
    let mut packedType := mkConst ``PUnit [.zero]
    for field in fields.reverse do
      packedType ← mkAppOptM ``PSigma #[some (← inferType field), some (← mkLambdaFVars #[field] packedType)]
    -- PLift makes the generated descriptor carrier Type-valued even when fields
    -- contain arbitrary Sort universes or only logical proofs.
    let fieldType ← mkAppOptM ``PLift #[some packedType]
    let fieldsName := destination.str "Fields"
    let encodeName := destination.str "toFields"
    let decodeName := destination.str "fromFields"
    let fromToName := destination.str "from_toFields"
    let toFromName := destination.str "to_fromFields"
    let bridgeName := destination.str "dictionaryBridge"
    addDefinition fieldsName ind.levelParams (← mkLambdaFVars params fieldType)
    let actualFields := mkAppN (mkConst fieldsName levels) params
    withLocalDeclD `dictionary dictionaryType fun dictionary => do
      let values := (List.range fields.size).toArray.map (mkProj name · dictionary)
      let packed ← packFields packedType values
      let lifted ← mkAppM ``PLift.up #[packed]
      addDefinition encodeName ind.levelParams (← mkLambdaFVars (params.push dictionary) lifted)
    withLocalDeclD `fields actualFields fun fields => do
      let mut current := mkProj ``PLift 0 fields
      let mut values := #[]
      for _ in *...ctor.numFields do
        values := values.push (mkProj ``PSigma 0 current)
        current := mkProj ``PSigma 1 current
      let dictionary := mkAppN (mkConst ctor.name levels) (params ++ values)
      addDefinition decodeName ind.levelParams (← mkLambdaFVars (params.push fields) dictionary)
    let encode := mkAppN (mkConst encodeName levels) params
    let decode := mkAppN (mkConst decodeName levels) params
    addInverse fromToName ind.levelParams params dictionaryType (fun value => pure (mkApp decode (mkApp encode value)))
    addInverse toFromName ind.levelParams params actualFields (fun value => pure (mkApp encode (mkApp decode value)))
    let bridge ← mkAppM ``Prototype.DictionaryBridge.mk
      #[encode, decode, mkAppN (mkConst fromToName levels) params, mkAppN (mkConst toFromName levels) params]
    addDefinition bridgeName ind.levelParams (← mkLambdaFVars params bridge)
  let fields := getStructureFields env name
  let labels := fields.toList.map (fun field => mkStrLit field.toString)
  addDefinition (destination.str "fieldNames") [] (← mkListLit (mkConst ``String) labels)
  addDefinition (destination.str "fieldCount") [] (mkNatLit ctor.numFields)

/-- Derive both typed dictionary/descriptor conversions and their exact laws.
An optional destination permits independent schemas without changing class search. -/
syntax (name := deriveDictionary) "derive_dictionary " ident (" as " ident)? : command

@[command_elab deriveDictionary] def elabDeriveDictionary : CommandElab := fun stx => do
  let `(derive_dictionary $source:ident $[as $target:ident]?) := stx | throwUnsupportedSyntax
  let name ← resolveGlobalConstNoOverload source
  let currentNamespace ← getCurrNamespace
  let destination := match target with
    | none => name
    | some target => currentNamespace ++ target.getId
  let previous ← getEnv
  try
    liftTermElabM <| generateDictionary name destination
  catch error =>
    setEnv previous
    throw error

end LeanPoo.Deriving
