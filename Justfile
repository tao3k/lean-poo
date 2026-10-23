set shell := ["bash", "-eu", "-c"]

# Full checks establish the Lake environment once; standalone recipes retain it.
lean := "lake env lean"

default:
    @just --list

# Check the source-owned graph and result types.
check-types:
    {{lean}} LeanPoo/C4/Types.lean

# Check C3 candidate merging independently.
check-merge: check-types
    lake build \
        LeanPoo.C4.Merge \
        LeanPoo.C4.Precedence \
        LeanPoo.C4.ReferenceMerge \
        LeanPoo.C4.MergeInvariant \
        LeanPoo.C4.Suffix \
        LeanPoo.C4.NodeCertificate \
        LeanPoo.C4.GraphCertificate \
        LeanPoo.C4.TraversalInvariant \
        LeanPoo.C4.SelectionInvariant \
        LeanPoo.C4.ParentInvariant \
        LeanPoo.C4.NormalizationInvariant \
        LeanPoo.C4.MetadataInvariant \
        LeanPoo.C4.ComputeInvariant \
        LeanPoo.C4.GraphComputeInvariant \
        LeanPoo.C4.ResolverInvariant \
        LeanPoo.C4.ReachabilityInvariant \
        LeanPoo.C4.ValidationInvariant \
        LeanPoo.C4.ExecutionInvariant \
        LeanPoo.C4.CertificateExpansion \
        LeanPoo.C4.NodeSoundness \
        LeanPoo.C4.OrdinaryNode \
        LeanPoo.C4.ResolverSoundness \
        LeanPoo.C4.AuditedResolver \
        LeanPoo.C4.Diagnostics \
        LeanPoo.C4.VerifiedOrder \
        LeanPoo.C4.OrderRelation \
        LeanPoo.C4.Renaming \
        LeanPoo.C4.Presentation \
        LeanPoo.C4.Relabeling \
        LeanPoo.Functional.Assembly \
        LeanPoo.Functional.Validation \
        LeanPoo.Functional.Codec \
        LeanPoo.Functional.ComputationBatch \
        LeanPoo.Functional.Requirements \
        LeanPoo.Functional.GuardedExtension \
        LeanPoo.Functional.GraphConstraints \
        LeanPoo.Functional.AnalyzedMigration \
        LeanPoo.Functional.DictionaryTransport \
        LeanPoo.Functional.SharedViews \
        LeanPoo.Functional.ViewRetarget \
        LeanPoo.Functional.StatefulValidation \
        LeanPoo.Functional.RequestHandling \
        LeanPoo.Functional.FocusedUpdate \
        LeanPoo.Functional.DispatchHandling \
        LeanPoo.Functional.RecursiveHandling \
        LeanPoo.Functional.RecursiveDispatch \
        LeanPoo.Functional.ReceiptAdmission \
        LeanPoo.Prototype.GeneralizedPrototype \
        LeanPoo.Prototype.GeneralizedInheritance \
        LeanPoo.Prototype.GeneralizedComponents \
        LeanPoo.Prototype.GeneralizedDependencies \
        LeanPoo.Prototype.GeneralizedChain \
        LeanPoo.Prototype.GeneralizedFork \
        LeanPoo.Prototype.GeneralizedContext \
        LeanPoo.Prototype.GeneralizedRevision \
        LeanPoo.Functional.GeneralizedGraph \
        LeanPoo.Functional.GeneralizedMOP \
        LeanPoo.Functional.GeneralizedFragments \
        LeanPoo.Functional.InheritedMOP \
        LeanPoo.Functional.ConstructionCache \
        LeanPoo.Functional.GenericFamily \
        LeanPoo.Functional.StagedPublication \
        LeanPoo.Functional.ServiceBundle \
        LeanPoo.Functional.DeclarativeMetadata \
        LeanPoo.Functional.ContractFamily \
        LeanPoo.Functional.ServiceMetadata \
        LeanPoo.Functional.ProjectedSelf \
        LeanPoo.Functional.CarrierMigration \
        LeanPoo.Functional.AccountMigration \
        LeanPoo.Prototype.FiniteClosure \
        LeanPoo.Functional.PositiveEquations \
        LeanPoo.Functional.CyclicPublication \
        LeanPoo.Functional.CyclicAccess \
        LeanPoo.Functional.IncrementalClosure \
        LeanPoo.Functional.ChunkedClosure \
        LeanPoo.Functional.QueueSelection \
        LeanPoo.Functional.ClosureLifecycle \
        LeanPoo.Functional.ClosureConstruction \
        LeanPoo.Functional.HybridClosure \
        LeanPoo.Functional.ClosureCosts \
        LeanPoo.Functional.ClosureScenarios \
        LeanPoo.Functional.ClosurePolicy \
        LeanPoo.Functional.InheritedSettlement \
        LeanPoo.Functional.ConstructionWorkflow \
        LeanPoo.Functional.PolicyPublication \
        LeanPoo.Functional.SharedSettlement \
        LeanPoo.Prototype.GeneralizedTariff \
        LeanPoo.Functional.RecordEvolution \
        LeanPoo.Functional.OrderedDictionary \
        LeanPoo.Functional.MetadataFamily \
        LeanPoo.Functional.MetadataClosure \
        LeanPoo.Functional.FactoryDispatchPublication \
        LeanPoo.Functional.DispatchExtension \
        LeanPoo.Functional.EnumeratedRequirements \
        LeanPoo.Deriving.DictionaryCompiler \
        LeanPoo.Functional.CertifiedRequirements \
        LeanPoo.Functional.CachedPreparation \
        LeanPoo.Functional.ConsumerRevision \
        LeanPoo.Functional.CertifiedView \
        LeanPoo.Functional.ResultView \
        LeanPoo.Functional.ResultIndex \
        LeanPoo.Functional.ViewComposition \
        LeanPoo.Functional.CertifiedObservation \
        LeanPoo.Functional.CertifiedConsumer \
        LeanPoo.Functional.ContextSlot \
        LeanPoo.Functional.ContractConsequence \
        LeanPoo.Functional.ContractJoin \
        LeanPoo.Functional.ContextView \
        LeanPoo.Functional.ContextObservation \
        LeanPoo.Functional.ContextPullback \
        LeanPoo.Functional.ObservedView \
        LeanPoo.Functional.BorrowedView \
        LeanPoo.Functional.Access \
        LeanPoo.Functional.View \
        LeanPoo.Functional.Observation \
        LeanPoo.Functional.Transport \
        LeanPoo.Functional.Reindex \
        LeanPoo.Functional.Presentation \
        LeanPoo.Functional.Relabeling \
        LeanPoo.Functional.Registry \
        LeanPoo.Functional.SharedRegistry \
        LeanPoo.Functional.RegistryPatch \
        LeanPoo.Functional.Overlay \
        LeanPoo.Functional.IndexedOverlay \
        LeanPoo.Functional.KeyIndex \
        LeanPoo.Functional.ScopedTransaction \
        LeanPoo.Functional.TransactionCheck \
        LeanPoo.Functional.IndexedTransaction \
        LeanPoo.Functional.IndexedRegistry \
        LeanPoo.Functional.RegistryBatch \
        LeanPoo.Functional.RegistryTransaction

# Check the C4 rewrite and its imports.
check-c4: check-merge
    lake build \
        LeanPoo.C4.Linearize \
        LeanPoo.C4.Ranked

# Check the paper's executable prototype nucleus.
check-mvp:
    lake build LeanPoo.Prototype.MVP
    {{lean}} Examples/PrototypeFunctions.lean
    {{lean}} Examples/RecordPrototype.lean

# Check generator application and delayed, non-function instances.
check-computation: check-mvp
    lake build LeanPoo.Prototype.Computation
    {{lean}} Examples/PrototypeCore.lean
    {{lean}} Examples/DelayedNumbers.lean

# Check first-class objects and delayed, self-dependent record slots.
check-first-class: check-computation
    lake build LeanPoo.Prototype.Object
    {{lean}} Examples/FirstClassObject.lean
    {{lean}} Examples/FirstClassRecord.lean

# Check the broader prototype composition rewrite.
check-prototype: check-first-class
    lake build \
        LeanPoo.Prototype.Class \
        LeanPoo.Prototype.Types \
        LeanPoo.Prototype.Lens \
        LeanPoo.Prototype.SkewLens \
        LeanPoo.Prototype.SlotSpec \
        LeanPoo.Prototype.Target

# Check typed generic selection over the object's existing slot evaluator.
check-generic: check-prototype
    lake build \
        LeanPoo.Object.Generic \
        LeanPoo.Object.MethodDictionary \
        LeanPoo.Object.Lens

# Check typed object declarations and C4-ordered slot resolution.
check-object: check-c4 check-generic
    lake build \
        LeanPoo.Object.Schema \
        LeanPoo.Object.Builder \
        LeanPoo.Object.Resolve \
        LeanPoo.Object.Indexed \
        LeanPoo.Object.Instance \
        LeanPoo.Object.Ranked \
        LeanPoo.Object.Incremental \
        LeanPoo.Object.Lazy \
        LeanPoo.Object.Prepare \
        LeanPoo.Object.Cache \
        LeanPoo.Object.Class \
        LeanPoo.Object.Migration \
        LeanPoo.Object.Initialization \
        LeanPoo.Object.MethodCombination \
        LeanPoo.Object.SimplePolicies \
        LeanPoo.Object.SimpleCombinationSemantics \
        LeanPoo.Object.QualifiedMethods \
        LeanPoo.Object.ShapeCache \
        LeanPoo.Object.Multimethod \
        LeanPoo.Object.PreparedMultimethod \
        LeanPoo.Object.MultimethodCombination \
        LeanPoo.Object.Subjective \
        LeanPoo.Object.DispatchTable \
        LeanPoo.Object.StaticDispatch \
        LeanPoo.Object.InlineDispatch \
        LeanPoo.Object.Prototype \
        LeanPoo.Object.Debug

# Check certified dependency propagation; opt into the impact trace on demand.
check-incremental verbose="false":
    lake build \
        LeanPoo.Object.Debug \
        LeanPoo.Proof.Revision \
        LeanPoo.Proof.Runtime \
        LeanPoo.Object.Lazy
    @if [ "{{verbose}}" = "true" ]; then LEANPOO_VERBOSE=1 timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/IncrementalObject.lean; else timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/IncrementalObject.lean; fi

# Check the public LeanPoo composition operations.
check-compose: check-object
    lake build \
        LeanPoo.Compose \
        LeanPoo.Slots \
        LeanPoo.Object.Memo \
        LeanPoo.Object.StrictBuilder \
        LeanPoo.Object.Definition \
        LeanPoo.Object.Nested \
        LeanPoo.Object.SpecificationComposition \
        LeanPoo.Object.SharedFamily \
        LeanPoo.Object.AncestryTransform \
        LeanPoo.Object.Renaming \
        LeanPoo.Object.Layout \
        LeanPoo.Object.Mutable \
        LeanPoo.Object.Upgrade \
        LeanPoo.Object.SortedInheritance \
        LeanPoo.Prototype.Mutable

# Check the proof-composition extension.
check-proof: check-compose
    lake build \
        LeanPoo.Prototype.SharedThunk \
        LeanPoo.Prototype.SharedThunkHeap \
        LeanPoo.Prototype.SharedCellRefinement \
        LeanPoo.Object.SharedRecursive \
        LeanPoo.Proof.Types \
        LeanPoo.Proof.Patch \
        LeanPoo.Proof.Reuse \
        LeanPoo.Proof.Batch \
        LeanPoo.Proof.Invalidation \
        LeanPoo.Proof.Object \
        LeanPoo.Proof.Revision \
        LeanPoo.Proof.Runtime \
        LeanPoo.Proof.Product

# Exercise the public invalidation report over a large independent corpus.
check-proof-reuse:
    lake build LeanPoo.Object.Debug
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/ProofReuseScale.lean

# Elaborate user-facing usage examples.
check-example: check-compose
    lake build Examples
    just --set lean "{{lean}}" _check-examples

# ComponentRounds shares the existing exclusive deadline phase. Its original
# 120s / 2GiB / heartbeat limits remain; the other ordinary proofs stay parallel.
[private]
_check-examples:
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Examples/SlotObservation.lean
    {{lean}} Examples/PrototypeCore.lean
    {{lean}} Examples/DictionaryRecords.lean
    {{lean}} Examples/MutableState.lean
    {{lean}} Examples/FunctionalPipeline.lean
    {{lean}} Examples/ValidationWorkflow.lean
    {{lean}} Examples/ValidatedConfiguration.lean
    {{lean}} Examples/IncrementalWorkflow.lean
    {{lean}} Examples/SharedReporting.lean
    {{lean}} Examples/DictionaryConsumers.lean
    {{lean}} Examples/ValidatedOrders.lean
    {{lean}} Examples/ResumableRequests.lean
    {{lean}} Examples/FocusedPricing.lean
    {{lean}} Examples/FocusedAllocation.lean
    {{lean}} Examples/DispatchWorkflow.lean
    {{lean}} Examples/RecoverableDispatch.lean
    {{lean}} Examples/RecursiveBilling.lean
    {{lean}} Examples/RecursiveDispatchWorkflow.lean
    {{lean}} Examples/ReceiptWorkflow.lean
    {{lean}} Examples/RecursiveCatalog.lean
    {{lean}} Examples/ConfigurationUpgrade.lean
    {{lean}} Examples/AtomicConfiguration.lean
    {{lean}} Examples/LayeredRouting.lean
    {{lean}} Examples/KeyedRebalance.lean
    {{lean}} Examples/MetadataDeployment.lean
    {{lean}} Examples/ClosedDeployment.lean
    {{lean}} Examples/ProtectedDispatch.lean
    {{lean}} Examples/PolicyDispatch.lean
    {{lean}} Examples/JointPublication.lean
    {{lean}} Examples/IntrospectiveExport.lean
    {{lean}} Examples/PreparedViews.lean
    {{lean}} Examples/CertifiedContextCache.lean
    {{lean}} Examples/DelayedNumbers.lean
    {{lean}} Examples/PrototypeFunctions.lean
    {{lean}} Examples/RecordPrototype.lean
    {{lean}} Examples/LensPrototype.lean
    {{lean}} Examples/GeneralizedService.lean
    {{lean}} Examples/GeneralizedCheckout.lean
    {{lean}} Examples/ComponentCheckout.lean
    {{lean}} Examples/DependentCheckout.lean
    {{lean}} Examples/ChainedCheckout.lean
    {{lean}} Examples/ForkedCheckout.lean
    {{lean}} Examples/SharedSettlement.lean
    {{lean}} Examples/PolicyPublication.lean
    {{lean}} Examples/ConstructionWorkflow.lean
    {{lean}} Examples/BuildCache.lean
    {{lean}} Examples/InheritedSettlement.lean
    {{lean}} Examples/ServiceBundle.lean
    {{lean}} Examples/ServiceMetadata.lean
    {{lean}} Examples/ContractFamily.lean
    {{lean}} Examples/AlignedServices.lean
    {{lean}} Examples/InheritedHooks.lean
    {{lean}} Examples/MetaBootstrap.lean
    {{lean}} Examples/RecursiveMetaprotocol.lean
    {{lean}} Examples/DeclaredMethods.lean
    {{lean}} Examples/TypedMethodDeclarations.lean
    {{lean}} Examples/RawArguments.lean
    {{lean}} Examples/MethodCompilation.lean
    {{lean}} Examples/CatalogReflection.lean
    {{lean}} Examples/DeclaredPrototypes.lean
    {{lean}} Examples/ClosedPrototypes.lean
    {{lean}} Examples/FeedbackServices.lean
    {{lean}} Examples/SharedFeedback.lean
    {{lean}} Examples/CachedFeedback.lean
    {{lean}} Examples/ComponentServices.lean
    {{lean}} Examples/ServiceRevisions.lean
    {{lean}} Examples/ComponentMembership.lean
    {{lean}} Examples/ComponentMigration.lean
    timeout --signal=TERM --kill-after=3s 120s {{lean}} -M 2048 -T 10000000 Examples/ComponentRounds.lean
    {{lean}} Examples/ComponentRequests.lean
    {{lean}} Examples/ApprovalRevision.lean
    {{lean}} Examples/SharedApprovals.lean
    {{lean}} Examples/JointComponentPublication.lean
    {{lean}} Examples/JointRounds.lean
    {{lean}} Examples/JointTopology.lean
    {{lean}} Examples/JointAdmission.lean
    {{lean}} Examples/JointInstallation.lean
    {{lean}} Examples/JointReceipts.lean
    {{lean}} Examples/JointCompetition.lean
    {{lean}} Examples/JointGenerations.lean
    {{lean}} Examples/JointRestaging.lean
    {{lean}} Examples/JointCoordination.lean
    {{lean}} Examples/ObjectContracts.lean
    {{lean}} Examples/ContainerContracts.lean
    {{lean}} Examples/VariantContracts.lean
    {{lean}} Examples/OptionalContracts.lean
    {{lean}} Examples/ClassContracts.lean
    {{lean}} Examples/ComputedContracts.lean
    {{lean}} Examples/RecursiveContracts.lean
    {{lean}} Examples/RecursiveRevisions.lean
    {{lean}} Examples/RecursiveMigrations.lean
    {{lean}} Examples/RecursiveTopologies.lean
    {{lean}} Examples/RecursiveStaging.lean
    {{lean}} Examples/RecursiveRestaging.lean
    {{lean}} Examples/RecursivePublication.lean
    {{lean}} Examples/RecursiveApprovals.lean
    {{lean}} Examples/RecursiveCompetition.lean
    {{lean}} Examples/RecursiveSubmissions.lean
    {{lean}} Examples/RecursiveRecovery.lean
    {{lean}} Examples/RecursiveCoordination.lean
    {{lean}} Examples/Parameters.lean
    {{lean}} Examples/Representation.lean
    {{lean}} Examples/GeneratedCalls.lean
    {{lean}} Examples/RecursiveGenerators.lean
    {{lean}} Examples/PrototypeTypes.lean
    {{lean}} Examples/RowTypes.lean
    {{lean}} Examples/ContractChecks.lean
    {{lean}} Examples/ServiceCollection.lean
    {{lean}} Examples/TableRevision.lean
    {{lean}} Examples/AccountMigration.lean
    {{lean}} Examples/CyclicAccess.lean
    {{lean}} Examples/ClosureLayouts.lean
    {{lean}} Examples/AdaptiveAccess.lean
    {{lean}} Examples/SelectedAccess.lean
    {{lean}} Examples/LifecycleAccess.lean
    {{lean}} Examples/ReshapedAccess.lean
    {{lean}} Examples/FirstClassObject.lean
    {{lean}} Examples/FirstClassRecord.lean
    {{lean}} Examples/MethodDictionary.lean
    {{lean}} Examples/ExtensibleDispatch.lean
    {{lean}} Examples/QualifiedCombination.lean
    {{lean}} Examples/BoundedDispatch.lean
    {{lean}} Examples/SharedFieldAccess.lean
    {{lean}} Examples/StaticMethodSelection.lean
    {{lean}} Examples/ProofReuse.lean
    {{lean}} Examples/LiveRevision.lean
    {{lean}} Examples/QuiescentUpgrade.lean
    {{lean}} Examples/SortedInheritance.lean
    {{lean}} Examples/ExtendedPrecedence.lean
    {{lean}} Examples/DebugTrace.lean
    {{lean}} Examples/LayeredObject.lean
    {{lean}} Examples/ObjectDefinition.lean
    {{lean}} Examples/NestedObjectDefinition.lean
    {{lean}} Examples/SpecificationComposition.lean
    {{lean}} Examples/ContextualFactories.lean
    {{lean}} Examples/SharedFamily.lean
    {{lean}} Examples/Renaming.lean
    {{lean}} Examples/ClassMigration.lean
    {{lean}} Examples/CertifiedInvalidation.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Examples/TargetAndWrapping.lean

# Check every behavioral and proof contract.
check-tests: check-proof
    just --set lean "{{lean}}" _check-contracts _check-diagnostics

[private]
_check-contracts:
    {{lean}} Tests/RecordCodec.lean
    {{lean}} Tests/CheckedMeta.lean
    {{lean}} Tests/DescriptorReflection.lean
    {{lean}} Tests/LinearState.lean
    {{lean}} Tests/FixedPoints.lean
    {{lean}} Tests/FiniteFix.lean
    {{lean}} Tests/RecursiveSemantics.lean
    {{lean}} Tests/SharedThunk.lean
    {{lean}} Tests/SharedCellRefinement.lean
    {{lean}} Tests/SharedRecursive.lean
    {{lean}} Tests/RecursiveCache.lean
    {{lean}} Tests/RecursiveCacheSemantics.lean
    {{lean}} Tests/DynamicDescriptor.lean
    {{lean}} Tests/DynamicDescriptorCompleteness.lean
    {{lean}} Tests/DynamicSchema.lean
    {{lean}} Tests/DynamicCodecSemantics.lean
    {{lean}} Tests/DynamicValueEquality.lean
    {{lean}} Tests/MutableRecord.lean
    {{lean}} Tests/MutableRecordSemantics.lean
    {{lean}} Tests/ConstructionSemantics.lean
    {{lean}} Tests/RecordDispatch.lean
    {{lean}} Tests/RecordComplexRelation.lean
    {{lean}} Tests/Trees.lean
    {{lean}} Tests/C3.lean
    {{lean}} Tests/C3Semantics.lean
    {{lean}} Tests/C3GraphSemantics.lean
    {{lean}} Tests/C3BatchCoherence.lean
    {{lean}} Tests/C3UnaryLeaf.lean
    {{lean}} Tests/C3TwoLeaf.lean
    {{lean}} Tests/C3LeafParents.lean
    {{lean}} Tests/C3DAG.lean
    {{lean}} Tests/C3CacheCoherence.lean
    {{lean}} Tests/C3Object.lean
    {{lean}} Tests/ObjectSemantics.lean
    {{lean}} Tests/RecursiveValidation.lean
    {{lean}} Tests/CallableObjects.lean
    {{lean}} Tests/CallableValidation.lean
    {{lean}} Tests/SourceDifferential.lean
    {{lean}} Tests/PrototypeChecks.lean
    {{lean}} Tests/DictionaryRecord.lean
    {{lean}} Tests/MetaPrototype.lean
    {{lean}} Tests/Representations.lean
    {{lean}} Tests/C4SuffixOrder.lean
    {{lean}} Tests/C4Ranked.lean
    {{lean}} Tests/C4Traversal.lean
    {{lean}} Tests/ComputedDefault.lean
    {{lean}} Tests/MapDeclaration.lean
    {{lean}} Tests/CompiledMemo.lean
    {{lean}} Tests/RankedObject.lean
    {{lean}} Tests/CertifiedCacheReuse.lean
    {{lean}} Tests/DescriptorClass.lean
    {{lean}} Tests/IntegratedPrototype.lean
    {{lean}} Tests/MethodDictionary.lean
    {{lean}} Tests/ObjectDefinition.lean
    {{lean}} Tests/StrictObjectDefinition.lean
    {{lean}} Tests/NestedObjectDefinition.lean
    {{lean}} Tests/ClassInstanceMethods.lean
    {{lean}} Tests/ClassInitialization.lean
    {{lean}} Tests/MethodCombination.lean
    {{lean}} Tests/SimpleMethodCombination.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/AlternativeCombination.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FactoryDispatchPublication.lean
    {{lean}} Tests/QualifiedMethodCombination.lean
    {{lean}} Tests/QualifiedCombination.lean
    {{lean}} Tests/ShapeCache.lean
    {{lean}} Tests/MultipleDispatch.lean
    {{lean}} Tests/MultimethodCombination.lean
    {{lean}} Tests/SubjectiveDispatch.lean
    {{lean}} Tests/DispatchTable.lean
    {{lean}} Tests/StaticDispatch.lean
    {{lean}} Tests/InlineDispatch.lean
    {{lean}} Tests/Chapter9Combination.lean
    {{lean}} Tests/SuffixLayout.lean
    {{lean}} Tests/MutableObject.lean
    {{lean}} Tests/SortedInheritance.lean
    {{lean}} Tests/ExtendedPrecedence.lean
    {{lean}} Tests/SuffixConsistency.lean
    {{lean}} Tests/NodeCertificate.lean
    {{lean}} Tests/GraphCertificate.lean
    {{lean}} Tests/ReferenceMerge.lean
    {{lean}} Tests/MergeInvariant.lean
    {{lean}} Tests/TraversalInvariant.lean
    {{lean}} Tests/SelectionInvariant.lean
    {{lean}} Tests/ParentInvariant.lean
    {{lean}} Tests/NormalizationInvariant.lean
    {{lean}} Tests/MetadataInvariant.lean
    {{lean}} Tests/ComputeInvariant.lean
    {{lean}} Tests/GraphComputeInvariant.lean
    {{lean}} Tests/ResolverInvariant.lean
    {{lean}} Tests/ReachabilityInvariant.lean
    {{lean}} Tests/ValidationInvariant.lean
    {{lean}} Tests/ExecutionInvariant.lean
    {{lean}} Tests/NodeSoundness.lean
    {{lean}} Tests/OrdinaryNode.lean
    {{lean}} Tests/AuditedResolver.lean
    {{lean}} Tests/Diagnostics.lean
    {{lean}} Tests/VerifiedOrder.lean
    {{lean}} Tests/OrderRelation.lean
    {{lean}} Tests/C4Renaming.lean
    {{lean}} Tests/C4Presentation.lean
    {{lean}} Tests/C4Relabeling.lean
    {{lean}} Tests/FunctionalRegistry.lean
    {{lean}} Tests/FunctionalSharedRegistry.lean
    {{lean}} Tests/FunctionalRegistryPatch.lean
    {{lean}} Tests/FunctionalOverlay.lean
    {{lean}} Tests/FunctionalIndexedOverlay.lean
    {{lean}} Tests/FunctionalKeyIndex.lean
    {{lean}} Tests/FunctionalScopedTransaction.lean
    {{lean}} Tests/FunctionalTransactionCheck.lean
    {{lean}} Tests/FunctionalIndexedTransaction.lean
    {{lean}} Tests/FunctionalIndexedRegistry.lean
    {{lean}} Tests/FunctionalRegistryBatch.lean
    {{lean}} Tests/FunctionalRegistryTransaction.lean
    {{lean}} Tests/ReusableContracts.lean
    {{lean}} Tests/FunctionalAssembly.lean
    {{lean}} Tests/FunctionalRequirements.lean
    {{lean}} Tests/FunctionalAbsence.lean
    {{lean}} Tests/FunctionalGraphMigration.lean
    {{lean}} Tests/FunctionalGraphConstraints.lean
    {{lean}} Tests/FunctionalDependencyAnalysis.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FunctionalValidation.lean
    {{lean}} Tests/FunctionalCodec.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FunctionalComputationBatch.lean
    {{lean}} Tests/FunctionalAnalyzedCache.lean
    {{lean}} Tests/FunctionalAnalyzedMigration.lean
    {{lean}} Tests/DictionaryCompiler.lean
    {{lean}} Tests/DictionaryBridge.lean
    {{lean}} Tests/DictionaryTransport.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FunctionalSharedViews.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FunctionalViewRetarget.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FunctionalStatefulValidation.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FunctionalRequestHandling.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FunctionalFocusedUpdate.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FunctionalDispatchHandling.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FunctionalRecursiveHandling.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/RecursiveDispatch.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/ReceiptAdmission.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FunctionalRecordEvolution.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FunctionalOrderedDictionary.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FunctionalReflectiveRequirements.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FunctionalMetadataClosure.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/FunctionalDispatchExtension.lean
    {{lean}} Tests/FunctionalCertifiedRequirements.lean
    {{lean}} Tests/FunctionalCachedPreparation.lean
    {{lean}} Tests/FunctionalConsumerRevision.lean
    {{lean}} Tests/FunctionalCertifiedView.lean
    {{lean}} Tests/FunctionalResultView.lean
    {{lean}} Tests/FunctionalResultIndex.lean
    {{lean}} Tests/FunctionalViewComposition.lean
    {{lean}} Tests/FunctionalCertifiedObservation.lean
    {{lean}} Tests/FunctionalCertifiedConsumer.lean
    {{lean}} Tests/FunctionalContextSlot.lean
    {{lean}} Tests/FunctionalTransformation.lean
    {{lean}} Tests/FunctionalTransformationProfiles.lean
    {{lean}} Tests/FunctionalSolverTransport.lean
    {{lean}} Tests/FunctionalFiniteDiagnostics.lean
    {{lean}} Tests/FunctionalContractConsequence.lean
    {{lean}} Tests/FunctionalContractJoin.lean
    {{lean}} Tests/FunctionalContextView.lean
    {{lean}} Tests/FunctionalContextObservation.lean
    {{lean}} Tests/FunctionalContextPullback.lean
    {{lean}} Tests/FunctionalObservedView.lean
    {{lean}} Tests/FunctionalBorrowedView.lean
    {{lean}} Tests/FunctionalMaintenance.lean
    {{lean}} Tests/FunctionalAccess.lean
    {{lean}} Tests/FunctionalView.lean
    {{lean}} Tests/FunctionalObservation.lean
    {{lean}} Tests/FunctionalTransport.lean
    {{lean}} Tests/FunctionalReindex.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/QuiescentUpgrade.lean
    {{lean}} Tests/MutablePrototype.lean
    {{lean}} Tests/TypedSlots.lean
    {{lean}} Tests/DeclarationBuilder.lean
    {{lean}} Tests/FocusedSpecification.lean
    {{lean}} Tests/SkewExtension.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/GeneralizedPrototype.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/GeneralizedComponents.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/GeneralizedDependencies.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/GeneralizedChain.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/GeneralizedFork.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/SharedSettlement.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/PolicyPublication.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/ConstructionWorkflow.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/InheritedSettlement.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/ConstructionCache.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/ServiceBundle.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/DeclarativeMetadata.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/AccountMigration.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/PositiveEquations.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/CyclicAccess.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/IncrementalClosure.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/ClosureCosts.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/HybridClosure.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/QueueSelection.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/ClosureLifecycle.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/ClosureConstruction.lean
    {{lean}} Tests/SpecificationFocus.lean
    {{lean}} Tests/SpecificationComposition.lean
    {{lean}} Tests/SharedFamily.lean
    {{lean}} Tests/AncestryTransform.lean
    {{lean}} Tests/Renaming.lean
    {{lean}} Tests/ClassMigration.lean
    timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/TargetPolicies.lean
    {{lean}} Tests/NestedPrototype.lean

# Check diagnostic contracts in a bounded Lean process.
check-debug verbose="false":
    lake build LeanPoo.Object.Debug
    @if [ "{{verbose}}" = "true" ]; then LEANPOO_VERBOSE=1 timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/DebugObject.lean; else timeout --signal=TERM --kill-after=3s 30s {{lean}} -M 2048 -T 10000000 Tests/DebugObject.lean; fi
    @debug_rc=0; timeout --signal=TERM --kill-after=1s 2s {{lean}} -M 2048 -T 10000000 Tests/DebugUnboundedBody.lean >/dev/null 2>&1 || debug_rc=$?; test "$debug_rc" -eq 124

# Compile the PO core, usage examples, and focused tests.
check-po: check-example check-tests check-docs

# Parse every maintained Org page, including the root and directory indexes.
check-docs:
    python3 tools/audit_poof.py --check
    python3 -m unittest tools.tests.org_reader -v
    python3 tools/check_docs.py

# Execute the reviewed original Racket blocks and compare all 24 Lean observations.
# A versioned source fixture removes the reference-checkout dependency in CI.
check-poof-source racket="racket":
    python3 tools/poof_source_check.py --racket "{{racket}}" --compare-lean

# Compare equality-only, hash-indexed ordered, and sorted-map construction.
benchmark-declaration:
    lake build LeanPoo.Object.Schema
    {{lean}} --run Benchmarks/DeclarationScale.lean

# Compare ordered replacement with checked unique-key definition construction.
benchmark-strict-definition:
    lake build LeanPoo.Object.StrictBuilder
    {{lean}} --run Benchmarks/StrictDefinitionScale.lean

# Compare repeated C4 recompilation with declaration-only plan revision.
benchmark-revision:
    lake build LeanPoo.Object.Resolve
    {{lean}} --run Benchmarks/RevisionScale.lean

# Compare repeated pairwise schema merging with one indexed pass.
benchmark-schema-merge:
    lake build LeanPoo.Object.Schema
    {{lean}} --run Benchmarks/SchemaMergeScale.lean

# Measure C4 traversal on deep and wide finite inheritance graphs.
benchmark-c4:
    lake build LeanPoo.C4.Linearize
    {{lean}} --run Benchmarks/C4Scale.lean

# Compare demand-driven, one-pass, and proof-backed indexed method resolution.
benchmark-memoization:
    lake build LeanPoo.Object.Memo
    {{lean}} --run Benchmarks/MemoizationScale.lean
    {{lean}} --run Benchmarks/MemoizationChainScale.lean

# Compare repeated standard-method assembly with one prepared effective method.
benchmark-effective-methods:
    lake build LeanPoo.Object.MultimethodCombination
    {{lean}} --run Benchmarks/PreparedDispatchScale.lean

# Compare direct selection, generic-function cache, and one call-site entry.
benchmark-inline-dispatch:
    lake build LeanPoo.Object.InlineDispatch
    {{lean}} --run Benchmarks/InlineDispatchScale.lean

# Compare runtime method-dictionary selection with a preselected Lean method.
benchmark-method-dictionary:
    lake build LeanPoo.Object.MethodDictionary
    {{lean}} --run Benchmarks/MethodDictionaryScale.lean

# Compare keyed lookup, checked offset access, and a monomorphic access site.
benchmark-layout:
    lake build LeanPoo.Object.Layout
    {{lean}} --run Benchmarks/LayoutScale.lean

# Compare sequential layer installation with one private final allocation.
benchmark-mutable-prototype:
    lake build LeanPoo.Prototype.Mutable
    {{lean}} --run Benchmarks/MutablePrototypeScale.lean

# Measure warm check startup with identical selected targets and Lean transcripts.
benchmark-check-startup:
    python3 Benchmarks/CheckStartup.py

# Compare identical warm Lean file checks with one and four workers.
benchmark-check-atoms:
    lake env python3 Benchmarks/CheckAtomsStudy.py --output /tmp/lean-poo-check-atoms.json

# Share one configured Lean environment across the complete gate.
check:
    lake env just --set lean lean _check

[private]
_check:
    python3 tools/check_gate.py

# Build the complete Lean library.
build: check

# Remove generated Lean build artifacts.
clean:
    lake clean

# Existing bounded diagnostic recipes retain their memory/time limits.
[private]
_check-diagnostics:
    just --set lean "{{lean}}" check-incremental false check-proof-reuse check-debug false

# Native admission verifies semantics under both snapshot retention policies.
_check-native-registry:
    .lake/build/bin/indexedRegistryScale list 64 16 4 latest
    .lake/build/bin/indexedRegistryScale indexed 64 16 4 latest
    .lake/build/bin/indexedRegistryScale list 64 16 4 retained
    .lake/build/bin/indexedRegistryScale indexed 64 16 4 retained

# Scoped consumer admission: both paths, negative/positive scopes and first errors.

_check-native-scoped:
    .lake/build/bin/scopedTransactionScale full outside 64 16 4
    .lake/build/bin/scopedTransactionScale scoped outside 64 16 4
    .lake/build/bin/scopedTransactionScale full keys 64 16 4
    .lake/build/bin/scopedTransactionScale scoped keys 64 16 4
    .lake/build/bin/scopedTransactionScale full positive 64 16 4
    .lake/build/bin/scopedTransactionScale scoped positive 64 16 4
    .lake/build/bin/scopedTransactionScale full unknown 64 16 4
    .lake/build/bin/scopedTransactionScale scoped unknown 64 16 4

# Retained requested-key index admission, without timing thresholds.
_check-native-key-index:
    .lake/build/bin/keyIndexScale list outside 64 16 4
    .lake/build/bin/keyIndexScale indexed outside 64 16 4
    .lake/build/bin/keyIndexScale list keys 64 16 4
    .lake/build/bin/keyIndexScale indexed keys 64 16 4
    .lake/build/bin/keyIndexScale list early 64 16 4
    .lake/build/bin/keyIndexScale indexed early 64 16 4
    .lake/build/bin/keyIndexScale list late 64 16 4
    .lake/build/bin/keyIndexScale indexed late 64 16 4
    .lake/build/bin/keyIndexScale list unknown 64 16 4
    .lake/build/bin/keyIndexScale indexed unknown 64 16 4

# Cached tuple/proof reuse admission, without timing thresholds.
_check-native-cached:
    .lake/build/bin/cachedPreparationScale indexed outside 64 16 4
    .lake/build/bin/cachedPreparationScale cached outside 64 16 4
    .lake/build/bin/cachedPreparationScale indexed keys 64 16 4
    .lake/build/bin/cachedPreparationScale cached keys 64 16 4
    .lake/build/bin/cachedPreparationScale indexed early 64 16 4
    .lake/build/bin/cachedPreparationScale cached early 64 16 4
    .lake/build/bin/cachedPreparationScale indexed late 64 16 4
    .lake/build/bin/cachedPreparationScale cached late 64 16 4
    .lake/build/bin/cachedPreparationScale indexed unknown 64 16 4
    .lake/build/bin/cachedPreparationScale cached unknown 64 16 4

# Native built-data cache admission: retain positive and negative cost controls.
_check-native-context:
    .lake/build/bin/contextSlotScale uncached hit 0 4 32
    .lake/build/bin/contextSlotScale cached hit 0 4 32
    .lake/build/bin/contextSlotScale uncached hit 16 4 32
    .lake/build/bin/contextSlotScale cached hit 16 4 32
    .lake/build/bin/contextSlotScale uncached miss 16 4 32
    .lake/build/bin/contextSlotScale cached miss 16 4 32
    .lake/build/bin/contextSlotScale uncached blocks 16 4 32
    .lake/build/bin/contextSlotScale cached blocks 16 4 32

# Native named-value lookup controls; no timing threshold.
_check-native-result-index:
    .lake/build/bin/resultIndexScale list head uniform 8 32 17
    .lake/build/bin/resultIndexScale indexed head uniform 8 32 17
    .lake/build/bin/resultIndexScale list tail uniform 8 32 17
    .lake/build/bin/resultIndexScale indexed tail uniform 8 32 17
    .lake/build/bin/resultIndexScale list cycle uniform 8 32 17
    .lake/build/bin/resultIndexScale indexed cycle uniform 8 32 17
    .lake/build/bin/resultIndexScale list tail collision 8 32 17
    .lake/build/bin/resultIndexScale indexed tail collision 8 32 17
