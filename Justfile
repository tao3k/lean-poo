set shell := ["zsh", "-eu", "-c"]

default:
    @just --list

# Check the source-owned graph and result types.
check-types:
    lake env lean LeanPoo/C4/Types.lean

# Check C3 candidate merging independently.
check-merge: check-types
    lake build LeanPoo.C4.Merge

# Check the C4 rewrite and its imports.
check-c4: check-merge
    lake build LeanPoo.C4.Linearize
    lake env lean Examples/C4SuffixOrder.lean

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
    lake build LeanPoo.Prototype.SlotSpec

# Check typed generic selection over the object's existing slot evaluator.
check-generic: check-prototype
    lake build LeanPoo.Object.Generic
    lake build LeanPoo.Object.Lens

# Check typed object declarations and C4-ordered slot resolution.
check-object: check-c4 check-generic
    lake build LeanPoo.Object.Schema
    lake build LeanPoo.Object.Resolve
    lake build LeanPoo.Object.Instance
    lake build LeanPoo.Object.Prepare
    lake build LeanPoo.Object.Cache
    lake build LeanPoo.Object.Class
    lake build LeanPoo.Object.Prototype
    lake build LeanPoo.Object.Debug
    lake env lean Examples/ComputedDefault.lean
    lake env lean Examples/MapDeclaration.lean

# Check the public LeanPoo composition operations.
check-compose: check-object
    lake build LeanPoo.Compose
    lake build LeanPoo.Slots
    lake build LeanPoo.Object.Memo
    lake build LeanPoo.Object.Mutable

# Check the proof-composition extension.
check-proof: check-compose
    lake build LeanPoo.Proof.Types
    lake build LeanPoo.Proof.Patch
    lake build LeanPoo.Proof.Reuse
    lake build LeanPoo.Proof.Batch
    lake build LeanPoo.Proof.Invalidation
    lake build LeanPoo.Proof.Object
    lake build LeanPoo.Proof.Product
    just check-proof-reuse

# Exercise the public invalidation report over a large independent corpus.
check-proof-reuse:
    lake build LeanPoo.Object.Debug
    timeout --signal=TERM --kill-after=3s 30s lake env lean -M 2048 -T 10000000 Examples/ProofReuseScale.lean

# Elaborate the independent PO examples.
check-example: check-compose
    lake env lean Examples/PrototypeCore.lean
    lake env lean Examples/DelayedNumbers.lean
    lake env lean Examples/PrototypeFunctions.lean
    lake env lean Examples/RecordPrototype.lean
    lake env lean Examples/LensPrototype.lean
    lake env lean Examples/FirstClassObject.lean
    lake env lean Examples/FirstClassRecord.lean
    lake env lean Examples/DescriptorClass.lean
    lake env lean Examples/MutableObject.lean
    lake env lean Examples/TypedSlots.lean
    lake env lean Examples/LayeredObject.lean
    lake env lean Examples/IntegratedPrototype.lean
    just check-debug

# Run diagnostic object examples in a bounded Lean process.
check-debug:
    lake build LeanPoo.Object.Debug
    timeout --signal=TERM --kill-after=3s 30s lake env lean -M 2048 -T 10000000 Examples/DebugObject.lean
    @debug_rc=0; timeout --signal=TERM --kill-after=1s 2s lake env lean -M 2048 -T 10000000 Examples/DebugUnboundedBody.lean >/dev/null 2>&1 || debug_rc=$?; test "$debug_rc" -eq 124

# Compile the complete executable PO core and its usage examples.
check-po: check-example check-docs

# Parse every maintained Org page, including the root README.
check-docs:
    emacs --batch -Q --eval '(progn (require (quote org-element)) (dolist (file (cons "README.org" (directory-files-recursively "docs" "\\.org$"))) (with-temp-buffer (insert-file-contents file) (org-mode) (org-element-parse-buffer))) (princ "ORG-OK"))'

# Measure wide declaration construction separately from correctness checks.
benchmark-declaration:
    lake build LeanPoo.Object.Schema
    lake env lean --run Examples/DeclarationScale.lean

check: check-proof check-example check-docs
    lake build

# Build the complete Lean library.
build: check

# Remove generated Lean build artifacts.
clean:
    lake clean
