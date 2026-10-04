set shell := ["zsh", "-eu", "-c"]

default:
    @just --list

# Check the source-owned graph and result types.
check-types:
    lake env lean LeanPoo/C4/Types.lean

# Check C3 candidate merging independently.
check-merge: check-types
    lake build LeanPoo.C4.Merge
    lake build LeanPoo.C4.Precedence
    lake build LeanPoo.C4.ReferenceMerge
    lake build LeanPoo.C4.MergeInvariant
    lake build LeanPoo.C4.Suffix
    lake build LeanPoo.C4.NodeCertificate
    lake build LeanPoo.C4.GraphCertificate
    lake build LeanPoo.C4.TraversalInvariant
    lake build LeanPoo.C4.SelectionInvariant
    lake build LeanPoo.C4.ParentInvariant
    lake build LeanPoo.C4.NormalizationInvariant
    lake build LeanPoo.C4.MetadataInvariant
    lake build LeanPoo.C4.ComputeInvariant

# Check the C4 rewrite and its imports.
check-c4: check-merge
    lake build LeanPoo.C4.Linearize
    lake build LeanPoo.C4.Ranked

# Check the paper's executable prototype nucleus.
check-mvp:
    lake build LeanPoo.Prototype.MVP
    lake env lean Examples/PrototypeFunctions.lean
    lake env lean Examples/RecordPrototype.lean

# Check generator application and delayed, non-function instances.
check-computation: check-mvp
    lake build LeanPoo.Prototype.Computation
    lake env lean Examples/PrototypeCore.lean
    lake env lean Examples/DelayedNumbers.lean

# Check first-class objects and delayed, self-dependent record slots.
check-first-class: check-computation
    lake build LeanPoo.Prototype.Object
    lake env lean Examples/FirstClassObject.lean
    lake env lean Examples/FirstClassRecord.lean

# Check the broader prototype composition rewrite.
check-prototype: check-first-class
    lake build LeanPoo.Prototype.Class
    lake build LeanPoo.Prototype.Types
    lake build LeanPoo.Prototype.Lens
    lake build LeanPoo.Prototype.SkewLens
    lake build LeanPoo.Prototype.SlotSpec
    lake build LeanPoo.Prototype.Target

# Check typed generic selection over the object's existing slot evaluator.
check-generic: check-prototype
    lake build LeanPoo.Object.Generic
    lake build LeanPoo.Object.MethodDictionary
    lake build LeanPoo.Object.Lens

# Check typed object declarations and C4-ordered slot resolution.
check-object: check-c4 check-generic
    lake build LeanPoo.Object.Schema
    lake build LeanPoo.Object.Builder
    lake build LeanPoo.Object.Resolve
    lake build LeanPoo.Object.Indexed
    lake build LeanPoo.Object.Instance
    lake build LeanPoo.Object.Ranked
    lake build LeanPoo.Object.Incremental
    lake build LeanPoo.Object.Lazy
    lake build LeanPoo.Object.Prepare
    lake build LeanPoo.Object.Cache
    lake build LeanPoo.Object.Class
    lake build LeanPoo.Object.Migration
    lake build LeanPoo.Object.Initialization
    lake build LeanPoo.Object.MethodCombination
    lake build LeanPoo.Object.QualifiedMethods
    lake build LeanPoo.Object.ShapeCache
    lake build LeanPoo.Object.Multimethod
    lake build LeanPoo.Object.PreparedMultimethod
    lake build LeanPoo.Object.MultimethodCombination
    lake build LeanPoo.Object.Subjective
    lake build LeanPoo.Object.DispatchTable
    lake build LeanPoo.Object.StaticDispatch
    lake build LeanPoo.Object.InlineDispatch
    lake build LeanPoo.Object.Prototype
    lake build LeanPoo.Object.Debug

# Check certified dependency propagation; opt into the impact trace on demand.
check-incremental verbose="false":
    lake build LeanPoo.Object.Debug
    lake build LeanPoo.Proof.Revision
    lake build LeanPoo.Proof.Runtime
    lake build LeanPoo.Object.Lazy
    @if [ "{{verbose}}" = "true" ]; then LEANPOO_VERBOSE=1 timeout --signal=TERM --kill-after=3s 30s lake env lean -M 2048 -T 10000000 Tests/IncrementalObject.lean; else timeout --signal=TERM --kill-after=3s 30s lake env lean -M 2048 -T 10000000 Tests/IncrementalObject.lean; fi

# Check the public LeanPoo composition operations.
check-compose: check-object
    lake build LeanPoo.Compose
    lake build LeanPoo.Slots
    lake build LeanPoo.Object.Memo
    lake build LeanPoo.Object.StrictBuilder
    lake build LeanPoo.Object.Definition
    lake build LeanPoo.Object.Nested
    lake build LeanPoo.Object.SpecificationComposition
    lake build LeanPoo.Object.SharedFamily
    lake build LeanPoo.Object.AncestryTransform
    lake build LeanPoo.Object.Renaming
    lake build LeanPoo.Object.Layout
    lake build LeanPoo.Object.Mutable
    lake build LeanPoo.Object.Upgrade
    lake build LeanPoo.Object.SortedInheritance
    lake build LeanPoo.Prototype.Mutable

# Check the proof-composition extension.
check-proof: check-compose
    lake build LeanPoo.Proof.Types
    lake build LeanPoo.Proof.Patch
    lake build LeanPoo.Proof.Reuse
    lake build LeanPoo.Proof.Batch
    lake build LeanPoo.Proof.Invalidation
    lake build LeanPoo.Proof.Object
    lake build LeanPoo.Proof.Revision
    lake build LeanPoo.Proof.Runtime
    lake build LeanPoo.Proof.Product

# Exercise the public invalidation report over a large independent corpus.
check-proof-reuse:
    lake build LeanPoo.Object.Debug
    timeout --signal=TERM --kill-after=3s 30s lake env lean -M 2048 -T 10000000 Tests/ProofReuseScale.lean

# Elaborate user-facing usage examples.
check-example: check-compose
    lake env lean Examples/PrototypeCore.lean
    lake env lean Examples/DelayedNumbers.lean
    lake env lean Examples/PrototypeFunctions.lean
    lake env lean Examples/RecordPrototype.lean
    lake env lean Examples/LensPrototype.lean
    lake env lean Examples/FirstClassObject.lean
    lake env lean Examples/FirstClassRecord.lean
    lake env lean Examples/MethodDictionary.lean
    lake env lean Examples/ExtensibleDispatch.lean
    lake env lean Examples/QualifiedCombination.lean
    lake env lean Examples/BoundedDispatch.lean
    lake env lean Examples/SharedFieldAccess.lean
    lake env lean Examples/StaticMethodSelection.lean
    lake env lean Examples/ProofReuse.lean
    lake env lean Examples/LiveRevision.lean
    lake env lean Examples/QuiescentUpgrade.lean
    lake env lean Examples/SortedInheritance.lean
    lake env lean Examples/ExtendedPrecedence.lean
    lake env lean Examples/DebugTrace.lean
    lake env lean Examples/LayeredObject.lean
    lake env lean Examples/ObjectDefinition.lean
    lake env lean Examples/NestedObjectDefinition.lean
    lake env lean Examples/SpecificationComposition.lean
    lake env lean Examples/SharedFamily.lean
    lake env lean Examples/Renaming.lean
    lake env lean Examples/ClassMigration.lean
    lake env lean Examples/CertifiedInvalidation.lean
    timeout --signal=TERM --kill-after=3s 30s lake env lean -M 2048 -T 10000000 Examples/TargetAndWrapping.lean

# Check every behavioral and proof contract.
check-tests: check-proof
    lake env lean Tests/C4SuffixOrder.lean
    lake env lean Tests/C4Ranked.lean
    lake env lean Tests/C4Traversal.lean
    lake env lean Tests/ComputedDefault.lean
    lake env lean Tests/MapDeclaration.lean
    lake env lean Tests/CompiledMemo.lean
    lake env lean Tests/RankedObject.lean
    lake env lean Tests/CertifiedCacheReuse.lean
    lake env lean Tests/DescriptorClass.lean
    lake env lean Tests/IntegratedPrototype.lean
    lake env lean Tests/MethodDictionary.lean
    lake env lean Tests/ObjectDefinition.lean
    lake env lean Tests/StrictObjectDefinition.lean
    lake env lean Tests/NestedObjectDefinition.lean
    lake env lean Tests/ClassInstanceMethods.lean
    lake env lean Tests/ClassInitialization.lean
    lake env lean Tests/MethodCombination.lean
    lake env lean Tests/SimpleMethodCombination.lean
    lake env lean Tests/QualifiedMethodCombination.lean
    lake env lean Tests/QualifiedCombination.lean
    lake env lean Tests/ShapeCache.lean
    lake env lean Tests/MultipleDispatch.lean
    lake env lean Tests/MultimethodCombination.lean
    lake env lean Tests/SubjectiveDispatch.lean
    lake env lean Tests/DispatchTable.lean
    lake env lean Tests/StaticDispatch.lean
    lake env lean Tests/InlineDispatch.lean
    lake env lean Tests/Chapter9Combination.lean
    lake env lean Tests/SuffixLayout.lean
    lake env lean Tests/MutableObject.lean
    lake env lean Tests/SortedInheritance.lean
    lake env lean Tests/ExtendedPrecedence.lean
    lake env lean Tests/SuffixConsistency.lean
    lake env lean Tests/NodeCertificate.lean
    lake env lean Tests/GraphCertificate.lean
    lake env lean Tests/ReferenceMerge.lean
    lake env lean Tests/MergeInvariant.lean
    lake env lean Tests/TraversalInvariant.lean
    lake env lean Tests/SelectionInvariant.lean
    lake env lean Tests/ParentInvariant.lean
    lake env lean Tests/NormalizationInvariant.lean
    lake env lean Tests/MetadataInvariant.lean
    lake env lean Tests/ComputeInvariant.lean
    timeout --signal=TERM --kill-after=3s 30s lake env lean -M 2048 -T 10000000 Tests/QuiescentUpgrade.lean
    lake env lean Tests/MutablePrototype.lean
    lake env lean Tests/TypedSlots.lean
    lake env lean Tests/DeclarationBuilder.lean
    lake env lean Tests/FocusedSpecification.lean
    lake env lean Tests/SkewExtension.lean
    lake env lean Tests/SpecificationFocus.lean
    lake env lean Tests/SpecificationComposition.lean
    lake env lean Tests/SharedFamily.lean
    lake env lean Tests/AncestryTransform.lean
    lake env lean Tests/Renaming.lean
    lake env lean Tests/ClassMigration.lean
    timeout --signal=TERM --kill-after=3s 30s lake env lean -M 2048 -T 10000000 Tests/TargetPolicies.lean
    lake env lean Tests/NestedPrototype.lean
    just check-incremental
    just check-proof-reuse
    just check-debug

# Check diagnostic contracts in a bounded Lean process.
check-debug verbose="false":
    lake build LeanPoo.Object.Debug
    @if [ "{{verbose}}" = "true" ]; then LEANPOO_VERBOSE=1 timeout --signal=TERM --kill-after=3s 30s lake env lean -M 2048 -T 10000000 Tests/DebugObject.lean; else timeout --signal=TERM --kill-after=3s 30s lake env lean -M 2048 -T 10000000 Tests/DebugObject.lean; fi
    @debug_rc=0; timeout --signal=TERM --kill-after=1s 2s lake env lean -M 2048 -T 10000000 Tests/DebugUnboundedBody.lean >/dev/null 2>&1 || debug_rc=$?; test "$debug_rc" -eq 124

# Compile the PO core, usage examples, and focused tests.
check-po: check-example check-tests check-docs

# Parse every maintained Org page, including the root and directory indexes.
check-docs:
    emacs --batch -Q --eval '(progn (require (quote org-element)) (dolist (file (append (list "README.org" "Examples/README.org" "Tests/README.org" "Benchmarks/README.org") (directory-files-recursively "docs" "\\.org$"))) (with-temp-buffer (insert-file-contents file) (org-mode) (org-element-parse-buffer))) (princ "ORG-OK"))'

# Compare equality-only, hash-indexed ordered, and sorted-map construction.
benchmark-declaration:
    lake build LeanPoo.Object.Schema
    lake env lean --run Benchmarks/DeclarationScale.lean

# Compare ordered replacement with checked unique-key definition construction.
benchmark-strict-definition:
    lake build LeanPoo.Object.StrictBuilder
    lake env lean --run Benchmarks/StrictDefinitionScale.lean

# Compare repeated C4 recompilation with declaration-only plan revision.
benchmark-revision:
    lake build LeanPoo.Object.Resolve
    lake env lean --run Benchmarks/RevisionScale.lean

# Compare repeated pairwise schema merging with one indexed pass.
benchmark-schema-merge:
    lake build LeanPoo.Object.Schema
    lake env lean --run Benchmarks/SchemaMergeScale.lean

# Measure C4 traversal on deep and wide finite inheritance graphs.
benchmark-c4:
    lake build LeanPoo.C4.Linearize
    lake env lean --run Benchmarks/C4Scale.lean

# Compare demand-driven, one-pass, and proof-backed indexed method resolution.
benchmark-memoization:
    lake build LeanPoo.Object.Memo
    lake env lean --run Benchmarks/MemoizationScale.lean
    lake env lean --run Benchmarks/MemoizationChainScale.lean

# Compare repeated standard-method assembly with one prepared effective method.
benchmark-effective-methods:
    lake build LeanPoo.Object.MultimethodCombination
    lake env lean --run Benchmarks/PreparedDispatchScale.lean

# Compare direct selection, generic-function cache, and one call-site entry.
benchmark-inline-dispatch:
    lake build LeanPoo.Object.InlineDispatch
    lake env lean --run Benchmarks/InlineDispatchScale.lean

# Compare runtime method-dictionary selection with a preselected Lean method.
benchmark-method-dictionary:
    lake build LeanPoo.Object.MethodDictionary
    lake env lean --run Benchmarks/MethodDictionaryScale.lean

# Compare keyed lookup, checked offset access, and a monomorphic access site.
benchmark-layout:
    lake build LeanPoo.Object.Layout
    lake env lean --run Benchmarks/LayoutScale.lean

# Compare sequential layer installation with one private final allocation.
benchmark-mutable-prototype:
    lake build LeanPoo.Prototype.Mutable
    lake env lean --run Benchmarks/MutablePrototypeScale.lean

check: check-example check-tests check-docs
    lake build

# Build the complete Lean library.
build: check

# Remove generated Lean build artifacts.
clean:
    lake clean
