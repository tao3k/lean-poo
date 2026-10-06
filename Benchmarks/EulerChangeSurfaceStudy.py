#!/usr/bin/env python3
"""Read-only source census and lexical call-site inventory, not an impact proof."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PIN = "f9e8bc5b38b6e212696e8a30e3e91517af887bbd"
POOF_PIN = "9affa8fbbb4f12cbd98cb97f8b8b84474fc39429"
DEFINITION = "Euler/PacketInitializedCorrectionNorms.lean"
NAMES = ["initializedCorrection_background", "initializedCorrection_background_derivative",
         "initializedCorrection_drift", "initializedCorrection_residual"]
CANDIDATES = ["SourceCoefficientAgreement", "initializedCorrectionData", "velocityMap"]


def git(reference, *args):
    return subprocess.check_output(["git", "-C", str(reference), *args])


def paper_cache_audit():
    reference = ROOT / ".data/poof"
    if git(reference, "rev-parse", "HEAD").decode().strip() != POOF_PIN or git(reference, "status", "--porcelain"):
        raise ValueError("POOF source must match the clean pinned reference")
    path = reference / "poof.scrbl"
    raw = path.read_bytes()
    rows = raw.decode().splitlines()
    tokens = ["@subsection{Cache invalidation}", "and let the users explicitly insert any cache desired.",
              "At the opposite end of the spectrum, the object system may assume purity-by-default",
              "must be pervasive in the entire language, not just the object system implementation,"]
    located = {}
    for token in tokens:
        lines = [i+1 for i, row in enumerate(rows) if token in row]
        if len(lines) != 1:
            raise ValueError(f"Expected one POOF cache token: {token}")
        located[token] = lines[0]
    return {"repository": "metareflection/poof", "commit": POOF_PIN,
            "file": ".data/poof/poof.scrbl", "sha256": hashlib.sha256(raw).hexdigest(),
            "token_lines": located, "scope": "Local original paper source; cache policy discussion, not a benchmark prediction or whole-language implementation"}


def paper_view_composition_audit():
    audit = paper_cache_audit()
    raw = (ROOT / audit["file"]).read_text()
    tokens = ["The lens, passed below as two function arguments", "it may be a composition of some of the above and more."]
    located = {}
    for token in tokens:
        lines = [i+1 for i, row in enumerate(raw.splitlines()) if token in row]
        if len(lines) != 1:
            raise ValueError(f"Expected one POOF composition token: {token}")
        located[token] = lines[0]
    audit["view_composition_token_lines"] = located
    audit["scope"] = "Original generalized prototype getter/composition discussion; local closed named-view laws do not implement lens setters or generalized prototype conformance"
    return audit


def paper_record_index_audit():
    audit = paper_cache_audit()
    rows = (ROOT / audit["file"]).read_text().splitlines()
    tokens = ["@subsubsection{Records as functions}", "by first encoding “records” of multiple named values as functions"]
    located = {}
    for token in tokens:
        matches = [i+1 for i, row in enumerate(rows) if token in row]
        if len(matches) != 1:
            raise ValueError(f"Expected one POOF named-record token: {token}")
        located[token] = matches[0]
    audit["named_record_token_lines"] = located
    audit["scope"] = "Original named-record and explicit-cache discussion; local immutable dependent hash access, not a paper runtime benchmark or generalized object implementation"
    return audit


def observation_bridge(reference):
    relative = "Euler/PacketInitializedResidualEquation.lean"
    raw = (reference / relative).read_bytes()
    text = raw.decode()
    names = ["toFieldTower_eq_of_path_eq", "initializedNormalizedField_path_eq",
             "initializedNormalizedField_tower_eq", "initializedCorrectionData_eq_coordinate"]
    declarations = {}
    for name in names:
        rows = [i for i, row in enumerate(text.splitlines(), 1)
                if re.match(r"theorem " + re.escape(name) + r"\b", row)]
        if len(rows) != 1:
            raise ValueError(f"Expected one declaration of {name}")
        declarations[name] = rows[0]
    return {"file": relative, "sha256": hashlib.sha256(raw).hexdigest(),
            "declarations": declarations,
            "scope": "Existing source bridge: path equality implies field-tower equality; correction-data equality is used by the residual identity",
            "external_lean_compilation": False,
            "proposed_contract": "Different representation families, fixed context/key/public observation family, pointwise observation equality on declared consumer keys",
            "euler_adapter_implemented": False}


def context_reindex(reference):
    sources = {}
    for relative, declaration, block in [
        ("Euler/PacketInitializedCorrectionData.lean", "initializedCorrectionData", [18, 21]),
        ("Euler/PacketForwardInitializedCorrectionData.lean", "forwardInitializedCorrectionData", [18, 20]),
    ]:
        raw = (reference / relative).read_bytes()
        rows = [i for i, row in enumerate(raw.decode().splitlines(), 1)
                if re.match(r"def " + re.escape(declaration) + r"\b", row)]
        if len(rows) != 1:
            raise ValueError(f"Expected one declaration of {declaration}")
        sources[relative] = {"sha256": hashlib.sha256(raw).hexdigest(),
                             "input_block_lines": block,
                             "declaration": declaration, "declaration_line": rows[0]}
    return {"sources": sources,
            "local_api": ["reindexProvider", "select_reindex", "assemble_reindex",
                          "Requirements.reindex", "Requirements.prepare_reindex",
                          "Requirements.results_reindex_type", "Requirements.projectedResults",
                          "Requirements.build_reindex"],
            "scope": "Complete provider/checklist adaptation along one explicit Outer-to-Context projection; exact first errors and projected dependent results",
            "projection_obligation": "Supply the entire old dependent context, including history/time guards and implicit instances; shared names do not establish a projection",
            "local_preparation_cases": 64, "outer_contexts_per_successful_case": 2,
            "analytic_equivalence_inferred": False, "euler_adapter_implemented": False,
            "external_lean_compilation": False, "runtime_benchmark": False}


def joint_certificate_audit(reference):
    """Hash-bound manual dependency reading; no elaboration or inferred graph."""
    records = {}
    for relative, declaration, fields in [
        ("Euler/PacketSourceEquations.lean", "SourceCoefficientAgreement", ["inverse", "strain"]),
        ("Euler/AllOrderDriftEquation.lean", "ApproximationResidual", ["pressure", "gradient", "equation"]),
        ("Euler/PacketInitializedResidualEquation.lean", "initializedApproximationResidual", []),
    ]:
        raw = (reference / relative).read_bytes()
        rows = raw.decode().splitlines()
        starts = [i for i, row in enumerate(rows, 1)
                  if re.match(r"(?:structure|def) " + re.escape(declaration) + r"\b", row)]
        if len(starts) != 1:
            raise ValueError(f"Expected one {declaration}")
        start = starts[0]
        field_rows = {}
        for field in fields:
            matches = [i for i, row in enumerate(rows, 1) if start < i < start + 20
                       and re.match(r"  " + re.escape(field) + r"\s*:", row)]
            if len(matches) != 1:
                raise ValueError(f"Expected one field {declaration}.{field}")
            field_rows[field] = matches[0]
        records[declaration] = {"file": relative, "sha256": hashlib.sha256(raw).hexdigest(),
                                "declaration_line": start, "field_lines": field_rows}
    constructor_rows = (reference / records['initializedApproximationResidual']['file']).read_text().splitlines()
    start = records['initializedApproximationResidual']['declaration_line']
    constructor = '\n'.join(constructor_rows[start-1:]).split('\nend ')[0]
    obligations = ['have hk0 : k ≠ 0', 'have hκ : |k⁻¹| ≤ 1',
                   'pressure := Pa.toFieldTower', 'gradient := ?_', 'equation := ?_',
                   'rw [initializedCorrectionData_eq_coordinate', 'Pa q hq t ht']
    for token in obligations:
        if token not in constructor:
            raise ValueError(f"Constructor obligation changed: {token}")
    return {"sources": records,
            "reviewed_dependencies": [
                {"field": "SourceCoefficientAgreement.inverse", "depends_on": ["M.FInv", "D.FInv.field", "D.clamp", "time interval M.T"]},
                {"field": "SourceCoefficientAgreement.strain", "depends_on": ["M.M.field", "D.M.field", "D.clamp", "time interval M.T"]},
                {"field": "ApproximationResidual.gradient", "depends_on": ["pressure.field", "A.κ", "A.direction", "period"]},
                {"field": "ApproximationResidual.equation", "depends_on": ["A.approximation", "A.residual", "A.metric", "pressure.realization", "q/hq", "t/ht", "hT"]}],
            "constructor_obligations": obligations,
            "reading_scope": "Manual direct-dependency reading of three declarations, validated by source hashes/tokens; not elaborated references, transitive dependency closure, or a migration proof",
            "local_api": ["Requirements.Certified", "Certified.build", "certify", "prepareCertified", "Certified.build_val", "prepareCertified_forget", "Certified.ext", "Certified.forget_injective", "prepareCertified_error_iff", "prepareCertified_congr"],
            "local_validation": {"preparations": 192, "joint_contract_cases": 8, "contexts_per_success": 3,
                                 "axiom_reports": 6, "heterogeneous_results": True, "duplicates_reversal_empty_missing": True},
            "mechanism": "Explicit joint Claim about the whole prepared tuple; supplied analytic proof retained with functions and erased at runtime. No automatic proof synthesis, dependency tracking, or runtime predicate validation",
            "scope": "Consumer contract only; Type-valued pressure data must remain in result tuples, while Prop-valued guards/certificates may enter Claim. Existing Factory.transport supports data-indexed Type witnesses",
            "euler_adapter_implemented": False, "external_lean_compilation": False,
            "actual_migrations": 0, "net_code_saved": None, "maintenance_hours_saved": None,
            "runtime_benchmark": False}


def context_observation_audit(reference):
    audit = observation_bridge(reference)
    rows = (reference / audit["file"]).read_text().splitlines()
    tokens = ["(h : G.path = H.path) : G.toFieldTower = H.toFieldTower", "Field.toFieldTower_eq_of_path_eq _ _", "(initializedNormalizedField_path_eq M D"]
    audit["bridge_token_lines"] = {}
    for token in tokens:
        lines = [i+1 for i, row in enumerate(rows) if token in row]
        if len(lines) != 1:
            raise ValueError(f"Expected one observation bridge token: {token}")
        audit["bridge_token_lines"][token] = lines
    audit["cache_limit"] = "Existing equality bridge only; no reference cache, computable context equality, redundant build, or external performance/maintenance gain demonstrated"
    return audit


def context_view_audit(reference):
    relative = "Euler/AllOrderDriftEquation.lean"
    raw = (reference / relative).read_bytes()
    rows = raw.decode().splitlines()
    blocks = {"pressure": ("def Budget.correctedPressureTower", "theorem Budget.correctedFieldTower_initial"),
              "gradient": ("theorem Budget.correctedPressureTower_gradient", "theorem ")}
    selected = {}
    for name, (start_token, end_token) in blocks.items():
        starts = [i for i, row in enumerate(rows) if row.startswith(start_token)]
        if len(starts) != 1:
            raise ValueError(f"Expected one {start_token}")
        start = starts[0]
        end = next(i for i in range(start+1, len(rows)) if rows[i].startswith(end_token))
        tokens = ["R.pressure.field", "R.pressure.realization", "R.pressure.value_eq"] if name == "pressure" else ["R.gradient t"]
        body = "\n".join(rows[start:end])
        for token in tokens:
            if token not in body:
                raise ValueError(f"Narrow field consumer changed: {token}")
        selected[name] = {"declaration_line": start+1,
                          "token_lines": {t: [i+1 for i in range(start,end) if t in rows[i]] for t in tokens}}
    return {"file": relative, "sha256": hashlib.sha256(raw).hexdigest(), "consumers": selected,
            "scope": "Direct named-field uses only; existing structure already projects fields. No dependency closure, redundant construction, executable adapter, or external cost reduction established"}


def context_slot_audit(reference):
    relative = "Euler/PacketInitializedResidualEquation.lean"
    raw = (reference / relative).read_bytes()
    rows = raw.decode().splitlines()
    starts = [i for i, row in enumerate(rows) if row.startswith("def initializedApproximationResidual ")]
    if len(starts) != 1:
        raise ValueError("Expected one initializedApproximationResidual")
    start = starts[0]
    end = next((i for i in range(start+1, len(rows)) if rows[i].startswith("end ")), len(rows))
    tokens = ["let Pa := initializedCoordinatePressureField", "pressure := Pa.toFieldTower",
              "Pa q hq t ht", "intro q hq t ht", "(N : ℕ)", "(hN : 1 ≤ N)", "(hk : 4 ≤ k)"]
    body = "\n".join(rows[start:end])
    for token in tokens:
        if token not in body:
            raise ValueError(f"Shared pressure construction changed: {token}")
    return {"file": relative, "sha256": hashlib.sha256(raw).hexdigest(), "declaration_line": start+1,
            "token_lines": {token: [i+1 for i in range(start, end) if token in rows[i]] for token in tokens},
            "scope": "Source already binds Pa once and uses it for tower/equation; direct source reading only. No redundant external execution, native timing, context memo benefit or migration inferred",
            "context_obligation": "All varying inputs must be represented in exact context; captured inputs remain fixed by the certified factory family. Matching N/k alone cannot justify reuse when other inputs vary; computable reference context equality not demonstrated"}


def certified_consumer_audit(reference):
    relative = "Euler/AllOrderDriftEquation.lean"
    raw = (reference / relative).read_bytes()
    rows = raw.decode().splitlines()
    name = "exists_exact_lifted_solution"
    starts = [i for i, row in enumerate(rows) if re.match(r"theorem " + name + r"\b", row)]
    if len(starts) != 1:
        raise ValueError(f"Expected one {name}")
    start = starts[0]
    end = next((i for i in range(start+1, len(rows)) if rows[i].startswith("end ")), len(rows))
    body = "\n".join(rows[start:end])
    tokens = ["(B : Budget period hT A)", "(R : ApproximationResidual period hT A)",
              "∃ (Z Q : FieldTower period T)", "(hq : 6 ≤ q)", "(ht : t ∈ Ioo 0 T)",
              "B.correctedFieldTower period", "B.correctedPressureTower period R",
              "B.correctedFieldTower_initial period", "B.correctedFieldTower_divergence period",
              "B.correctedPressureTower_gradient period R", "B.correctedFieldTower_error_energy period",
              "B.correctedFieldTower_hasDerivAt period R"]
    for token in tokens:
        if token not in body:
            raise ValueError(f"Joint construction changed: {token}")
    return {"file": relative, "sha256": hashlib.sha256(raw).hexdigest(), "declaration": name,
            "declaration_line": start+1,
            "token_lines": {token: [i+1 for i in range(start, end) if token in rows[i]] for token in tokens},
            "reviewed_output": "Two explicit field-tower data witnesses and five proof-producing calls, including paired energy bounds; shared period/time/data/order guards remain",
            "scope": "Direct source reading with token/hash guards; not elaboration, a Lean adapter, proof synthesis or a measured maintenance reduction"}


def certified_observation_audit(reference):
    relative = "Euler/PacketInitializedResidualEquation.lean"
    raw = (reference / relative).read_bytes()
    rows = raw.decode().splitlines()
    records = {}
    for name, tokens in [
        ("toFieldTower_eq_of_path_eq", ["{raw raw' : VectorField}", "(h : G.path = H.path)", "G.toFieldTower = H.toFieldTower"]),
        ("initializedNormalizedField_tower_eq", ["Field.toFieldTower_eq_of_path_eq", "initializedNormalizedField_path_eq"]),
        ("initializedCorrectionData_eq_coordinate", ["unfold initializedCorrectionData coordinateData correctionDataOfFields", "rw [initializedNormalizedField_tower_eq", "(hN : 1 ≤ N)", "(hk : 4 ≤ k)", "(hκ : |k⁻¹| ≤ 1)"]),
    ]:
        starts = [i for i, row in enumerate(rows) if re.match(r"theorem " + name + r"\b", row)]
        if len(starts) != 1:
            raise ValueError(f"Expected one {name}")
        start = starts[0]
        end = next((i for i in range(start+1, len(rows)) if re.match(r"(?:def|theorem) ", rows[i])), len(rows))
        body = "\n".join(rows[start:end])
        for token in tokens:
            if token not in body:
                raise ValueError(f"Observation bridge changed: {name}: {token}")
        records[name] = {"declaration_line": start+1,
                         "token_lines": {token: [i+1 for i in range(start, end) if token in rows[i]] for token in tokens}}
    return {"file": relative, "sha256": hashlib.sha256(raw).hexdigest(), "declarations": records,
            "scope": "Direct source equality chain from path to public field tower to correction data, with different raw field indices and explicit analytic guards; not elaborated/transitive dependencies or an adapter"}


def built_result_audit(reference):
    relative = "Euler/AllOrderDriftEquation.lean"
    raw = (reference / relative).read_bytes()
    rows = raw.decode().splitlines()
    consumers = {}
    for name, tokens in [
        ("Budget.correctedPressureTower", ["R.pressure.field", "R.pressure.realization", "R.pressure.value_eq"]),
        ("Budget.correctedPressureTower_gradient", ["R.gradient t", "gradientSpace period A.κ A.direction"]),
        ("Budget.correctedFieldTower_hasDerivAt", ["R.equation q hq t ht", "R.pressure.realization q", "q : ℕ", "hq : 6 ≤ q", "ht : t ∈ Ioo 0 T"]),
    ]:
        starts = [i for i, row in enumerate(rows) if re.match(r"(?:def|theorem) " + re.escape(name) + r"\b", row)]
        if len(starts) != 1:
            raise ValueError(f"Expected one {name}")
        start = starts[0]
        end = next((i for i in range(start+1, len(rows)) if re.match(r"(?:def|theorem) ", rows[i])), len(rows))
        body = "\n".join(rows[start:end])
        for token in tokens:
            if token not in body:
                raise ValueError(f"Built result obligation changed: {name}: {token}")
        consumers[name] = {"declaration_line": start+1,
                           "token_lines": {token: [i+1 for i in range(start, end) if token in rows[i]] for token in tokens}}
    return {"file": relative, "sha256": hashlib.sha256(raw).hexdigest(), "consumers": consumers,
            "scope": "Direct reading of named pressure data and joint gradient/equation evidence; not elaboration, transitive dependency closure, or evidence of redundant external factory execution"}


def narrow_consumer_audit(reference):
    relative = "Euler/PacketSourceEquations.lean"
    raw = (reference / relative).read_bytes()
    rows = raw.decode().splitlines()
    consumers = {}
    for name, field in [("sourceInverse_eq_mean", "inverse"), ("sourceStrain_eq_mean", "strain")]:
        starts = [i for i, row in enumerate(rows) if re.match(r"theorem " + name + r"\b", row)]
        if len(starts) != 1:
            raise ValueError(f"Expected one {name}")
        start = starts[0]
        end = next((i for i in range(start+1, len(rows)) if rows[i].startswith("theorem ")), len(rows))
        body = "\n".join(rows[start:end])
        token = f"A.{field} t x"
        if token not in body or "EulerMeanPacketProvider.Data.clamp_coe" not in body:
            raise ValueError(f"Consumer obligations changed: {name}")
        consumers[name] = {"declaration_line": start+1, "certificate_field": field,
                           "field_use_lines": [i+1 for i in range(start, end) if token in rows[i]],
                           "retained_obligations": ["dependent M/D types and instances", "time clamp equality"]}
    return {"file": relative, "sha256": hashlib.sha256(raw).hexdigest(), "consumers": consumers,
            "scope": "Manual direct source reading with declaration/token guards; not elaboration or transitive dependency closure"}


def consumer_time_audit(reference):
    relative = "Euler/PacketInitializedResidualEquation.lean"
    raw = (reference / relative).read_bytes()
    rows = raw.decode().splitlines()
    declarations = {}
    for name in ["initializedVelocityField", "initializedVelocityDerivativeField", "initializedVelocityField_time"]:
        matches = [i for i, row in enumerate(rows, 1)
                   if re.match(r"(?:def|theorem) " + name + r"\b", row)]
        if len(matches) != 1:
            raise ValueError(f"Expected one {name}")
        declarations[name] = matches[0]
    transport = [i for i, row in enumerate(rows, 1) if ".changeTime hTime" in row]
    derivative = [i for i, row in enumerate(rows, 1) if "Field.changeTime_derivative _ _ hTime" in row]
    if len(transport) != 2 or len(derivative) != 1:
        raise ValueError("Explicit time transports changed")
    return {"file": relative, "sha256": hashlib.sha256(raw).hexdigest(),
            "declarations": declarations, "change_time_lines": transport,
            "derivative_transport_lines": derivative,
            "scope": "Manual reading plus exact declaration/token checks; not elaborated implicit-instance or transitive dependency closure"}


def study(reference):
    if git(reference, "rev-parse", "HEAD").decode().strip() != PIN:
        raise ValueError("Reference pin mismatch")
    if git(reference, "status", "--porcelain=v1"):
        raise ValueError("Reference must remain clean")
    files = sorted(p for p in git(reference, "ls-files", "-z").decode().split("\0")
                   if p.endswith(".lean"))
    lines, groups, digest = 0, Counter(), hashlib.sha256()
    mentions = {name: [] for name in NAMES}
    candidates = {name: {"files": 0, "occurrences": 0, "sample": []} for name in CANDIDATES}
    for relative in files:
        raw = (reference / relative).read_bytes()
        digest.update(relative.encode() + b"\0" + hashlib.sha256(raw).digest())
        text = raw.decode()
        rows = text.splitlines()
        lines += len(rows)
        groups[relative.split("/", 1)[0]] += 1
        for name, item in candidates.items():
            count = len(re.findall(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])", text))
            if count:
                item["files"] += 1
                item["occurrences"] += count
                if len(item["sample"]) < 3:
                    item["sample"].append({"file": relative, "occurrences": count})
        if relative == DEFINITION:
            continue
        for name in NAMES:
            pattern = re.compile(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])")
            matches = [i for i, row in enumerate(rows, 1) if pattern.search(row)]
            if matches:
                mentions[name].append({"file": relative, "lines": matches})
    local = ["LeanPoo/Functional/View.lean", "Tests/FunctionalView.lean",
             "LeanPoo/Functional/Observation.lean", "Tests/FunctionalObservation.lean",
             "LeanPoo/Functional/Transport.lean", "Tests/FunctionalTransport.lean",
             "LeanPoo/Functional/Reindex.lean", "Tests/FunctionalReindex.lean",
             "LeanPoo/C4/Presentation.lean", "LeanPoo/Functional/Presentation.lean",
             "Tests/C4Presentation.lean", "LeanPoo/C4/Relabeling.lean",
             "LeanPoo/Functional/Relabeling.lean", "Tests/C4Relabeling.lean",
             "LeanPoo/Functional/Registry.lean", "Tests/FunctionalRegistry.lean",
             "LeanPoo/Functional/SharedRegistry.lean", "Tests/FunctionalSharedRegistry.lean",
             "LeanPoo/Functional/RegistryPatch.lean", "Tests/FunctionalRegistryPatch.lean",
             "LeanPoo/Functional/Overlay.lean", "Tests/FunctionalOverlay.lean",
             "LeanPoo/Functional/RegistryBatch.lean", "Tests/FunctionalRegistryBatch.lean",
             "LeanPoo/Functional/RegistryTransaction.lean", "Tests/FunctionalRegistryTransaction.lean",
             "LeanPoo/Functional/IndexedOverlay.lean", "Tests/FunctionalIndexedOverlay.lean",
             "LeanPoo/Functional/IndexedRegistry.lean", "Tests/FunctionalIndexedRegistry.lean",
             "LeanPoo/Functional/IndexedTransaction.lean", "Tests/FunctionalIndexedTransaction.lean",
             "LeanPoo/Functional/TransactionCheck.lean", "Tests/FunctionalTransactionCheck.lean",
             "LeanPoo/Functional/ScopedTransaction.lean", "Tests/FunctionalScopedTransaction.lean",
             "LeanPoo/Functional/KeyIndex.lean", "Tests/FunctionalKeyIndex.lean",
             "LeanPoo/Functional/CertifiedRequirements.lean", "Tests/FunctionalCertifiedRequirements.lean",
             "LeanPoo/Functional/CachedPreparation.lean", "Tests/FunctionalCachedPreparation.lean",
             "LeanPoo/Functional/ConsumerRevision.lean", "Tests/FunctionalConsumerRevision.lean",
             "LeanPoo/Functional/CertifiedView.lean", "Tests/FunctionalCertifiedView.lean",
             "LeanPoo/Functional/ResultView.lean", "Tests/FunctionalResultView.lean",
             "LeanPoo/Functional/CertifiedObservation.lean", "Tests/FunctionalCertifiedObservation.lean",
             "LeanPoo/Functional/CertifiedConsumer.lean", "Tests/FunctionalCertifiedConsumer.lean",
             "LeanPoo/Functional/ContextSlot.lean", "Tests/FunctionalContextSlot.lean",
             "LeanPoo/Functional/ContextView.lean", "Tests/FunctionalContextView.lean",
             "LeanPoo/Functional/ContextObservation.lean", "Tests/FunctionalContextObservation.lean",
             "LeanPoo/Functional/ContextPullback.lean", "Tests/FunctionalContextPullback.lean",
             "Benchmarks/ContextSlotScale.lean", "Benchmarks/ContextSlotStudy.py",
             "LeanPoo/Functional/ObservedView.lean", "Tests/FunctionalObservedView.lean",
             "LeanPoo/Functional/BorrowedView.lean", "Tests/FunctionalBorrowedView.lean",
             "LeanPoo/Functional/ViewComposition.lean", "Tests/FunctionalViewComposition.lean",
             "LeanPoo/Functional/ContractConsequence.lean", "Tests/FunctionalContractConsequence.lean",
             "LeanPoo/Functional/ContractJoin.lean", "Tests/FunctionalContractJoin.lean",
             "LeanPoo/Functional/ResultIndex.lean", "Tests/FunctionalResultIndex.lean"]
    return {
        "schema": "lean-poo.euler-change-surface.v1",
        "reference": {"repository": "openai/NavierStokesAndEuler", "commit": PIN,
                      "tracked_lean_files": len(files), "physical_lines": lines,
                      "files_by_top_level": dict(sorted(groups.items())),
                      "source_manifest_sha256": digest.hexdigest(),
                      "scope": "Git-tracked .lean files only; dependencies/generated/untracked files excluded"},
        "lexical_mentions": mentions,
        "candidate_interfaces": candidates,
        "candidate_limit": "All identifier-text occurrences, including defining files/comments; prioritization only, not evidence of interchangeable providers or C4 benefit",
        "mention_limit": "Identifier-text rows outside defining file, including possible comments; not elaborated references, dependency closure, or affected-file count",
        "result_index": {
            "paper_source": paper_record_index_audit(),
            "reference_audit": context_view_audit(reference),
            "local_api": ["ResultIndex", "ResultIndex.ofResults", "ResultIndex.find?", "ResultIndex.find?_present", "ResultIndex.find?_absent", "ResultIndex.get", "ResultIndex.get_eq", "ResultIndex.project", "ResultIndex.project_eq"],
            "tests": {"indices": 72, "queries": 288, "projections": 729, "projected_positions": 972, "contexts": 3, "forced_hash_collisions": True, "heterogeneous_dependent_values": True, "inconsistent_duplicate_first_occurrence": True, "missing_keys": True, "wrong_tuple_and_context_rejected": True, "joint_proof_transport_client": True, "axiom_reports": 4, "axioms": ["propext", "Classical.choice", "Quot.sound"]},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["LeanPoo/Functional/ResultIndex.lean", "Tests/FunctionalResultIndex.lean"]},
            "mechanism": "Build a dependent hash table once from exact built data, tail-first insertion preserves first source occurrence; retained named access/projection uses one hash lookup per requested position instead of a source-list scan",
            "cost": "Full source traversal and hash insertion at setup, map storage/value retention, hashing/collision costs and output tuple construction remain; duplicate target keys repeat lookups; changed data/context requires a new index",
            "limits": ["Reference already uses Lean structure projections; linear field scans or replaceable upstream access not established", "No automatic dependency graph, cache invalidation or integration; exact data/context index required", "No native timing, allocation or break-even measurement; collision correctness is not a speedup; Euler migrations 0, net lines and maintenance hours unmeasured"]},
        "contract_join": {
            "paper_source": paper_cache_audit(),
            "reference_audit": joint_certificate_audit(reference),
            "local_api": ["Certified.conjoin", "Certified.conjoin_factories", "Snapshot.conjoin", "Snapshot.conjoin_val", "ContextSlot.conjoin", "ContextSlot.conjoin_empty", "ContextSlot.conjoin_retained", "ContextSlot.conjoin_hit", "ContextSlot.conjoin_consume"],
            "tests": {"families": 8, "reads": 224, "hits": 112, "misses": 112, "traces": 4, "warm_modes": 2, "heterogeneous_retention": True, "dependent_output_uses_both_proofs": True, "post_join_consequence_hits": True, "wrong_family_and_context_rejected": True, "arbitrary_data_implication_counterexample": True, "axiom_reports": 6, "axiom_free_reports": 4},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["LeanPoo/Functional/ContractJoin.lean", "Tests/FunctionalContractJoin.lean"]},
            "mechanism": "Conjoin independently admitted joint proofs about explicitly equal complete factory tuples; retain left functions and cached values without re-preparing or rebuilding a joint certificate manually",
            "cost": "Explicit factory equality and both admission proofs are erased; slot Option/context wrapper is mapped, Results is not traversed; normal equality/miss builds/constructors remain",
            "limits": ["Exact full-family equality is required; equal names, context or Claim shapes do not suffice", "No general arbitrary-data implication from Left to Right is required or inferred; cached alignment justifies right admission", "Reference already has joint inverse/strain and pressure/gradient/equation structures; repeated admission or rebuild not established", "Explicit immutable cache policy extension; no full paper conformance or native time/allocation qualification; Euler integrations/migrations 0, net lines and hours unmeasured"]},
        "contract_consequence": {
            "paper_source": paper_cache_audit(),
            "reference_audit": joint_certificate_audit(reference),
            "local_api": ["Certified.entails", "Certified.entails_factories", "Certified.entails_trans", "Snapshot.entails", "Snapshot.entails_val", "ContextSlot.entails", "ContextSlot.entails_empty", "ContextSlot.entails_retained", "ContextSlot.entails_hit", "ContextSlot.entails_consume"],
            "tests": {"families": 8, "reads": 192, "hits": 104, "misses": 88, "traces": 3, "warm_modes": 2, "dependent_output": True, "chained_consequence_hits": True, "invalid_consequence_and_wrong_context_rejected": True, "axiom_reports": 7, "axiom_free_reports": 5},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["LeanPoo/Functional/ContractConsequence.lean", "Tests/FunctionalContractConsequence.lean"]},
            "mechanism": "Derive a new joint contract once while retaining exact factories and built data; compose logical consequences without projecting keys or observing values",
            "cost": "Proofs are erased; populated slot conversion maps its Option/context wrapper, without traversing Results or executing factories/observers/constructors; normal context equality, misses, retention and consumers remain",
            "limits": ["Caller supplies a valid implication over arbitrary data at each context; no stronger analytic fact is inferred", "Reference already carries inverse/strain and pressure/gradient/equation proofs; no repeated admission or avoidable rebuild established", "Lean-specific contract adaptation extends explicit immutable cache policy, not full paper conformance; native allocation/time and Euler code/maintenance savings unmeasured; integrations/migrations 0"]},
        "view_composition": {
            "paper_source": paper_view_composition_audit(),
            "reference_audit": context_view_audit(reference),
            "local_api": ["resultAt_project", "projectResults_trans", "factoryAt_project", "project_trans"],
            "tests": {"cases": 5184, "contexts": 3, "orderings": 3, "inconsistent_duplicates": True, "identity_counterexample": True, "axiom_reports": 4},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["LeanPoo/Functional/ViewComposition.lean", "Tests/FunctionalViewComposition.lean"]},
            "mechanism": "Direct final projection equals two-stage projection for arbitrary dependent values/functions; clients may omit the intermediate tuple and transport existing equalities",
            "structural_controls": {"positive_two_stage_direct_checks": [9, 1], "negative_two_stage_direct_checks": [13, 30], "scope": "Independent list scanner comparison counts, not native allocation or timing evidence"},
            "limits": ["Direct broad scans can cost more than repeated access to a small retained intermediate view", "Reference already uses nested named fields; avoidable intermediate projection not established", "No automatic rewrite, lens updates, runtime speedup or Euler migration; net lines and maintenance savings unmeasured"]},
        "borrowed_view": {
            "paper_source": paper_cache_audit(),
            "reference_audit": context_view_audit(reference),
            "shared_pressure_audit": context_slot_audit(reference),
            "local_api": ["ContextSlot.readView", "ContextSlot.readView_state", "ContextSlot.readView_value", "ContextSlot.consumeView", "ContextSlot.consumeView_value"],
            "tests": {"reads": 120, "hits": 113, "misses": 7, "views": 5, "observers": 2, "traces": 3, "dependent_proof_output": True, "inconsistent_duplicate_preserved_in_broad_cache": True, "axiom_reports": 3},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["LeanPoo/Functional/BorrowedView.lean", "Tests/FunctionalBorrowedView.lean"]},
            "mechanism": "Expose each consumer view while returning the original broad cache transition and hit flag; different views share one retained broad tuple",
            "cost": "Every request projects and observes its view and runs its constructor; misses build broad dependencies; broad tuple stays retained; source scans and view allocation remain",
            "limits": ["Existing reference consumers already share R and pressure Pa; no redundant external cache established", "No native timing or allocation qualification for borrowed views; old cache timings do not transfer", "Euler integrations and migrations 0; net lines and maintenance savings unmeasured"]},
        "observed_view": {
            "paper_source": paper_cache_audit(),
            "reference_audit": context_view_audit(reference),
            "local_api": ["resultAt_observe", "projectResults_observe", "Certified.observeProject", "Snapshot.observeProject", "Snapshot.observeProject_val", "ContextSlot.observeProject", "ContextSlot.observeProject_empty", "ContextSlot.observeProject_retained", "ContextSlot.observeProject_hit", "ContextSlot.observeProject_consume"],
            "tests": {"cases": 4608, "successes": 1944, "reads": 23328, "hits": 5832, "contexts": 3, "joint_proof_outputs": 3, "first_duplicate_observation": True, "axiom_reports": 7},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["LeanPoo/Functional/ObservedView.lean", "Tests/FunctionalObservedView.lean"]},
            "mechanism": "Project requested raw positions before observing them; one narrow public certificate and direct data consequence, without a broad public Claim or intermediate narrow raw Claim",
            "cost": "Source scans and projected/observed tuples remain; repeated requested keys repeat observations; no observation on unrequested source positions during conversion",
            "limits": ["Total pure observation functions and explicit public consequence required", "Reference already projects named pressure fields; redundant observation, external migration or savings not established", "This path has no native timing/allocation study; previous cache timings cannot be transferred; Euler migrations 0"]},
        "context_slot_native": {
            "paper_source": paper_cache_audit(),
            "reference_audit": context_slot_audit(reference),
            "local_receipt": "Benchmarks/receipts/context-slot-native-2026-10-05.json",
            "receipt_sha256": hashlib.sha256((ROOT / "Benchmarks/receipts/context-slot-native-2026-10-05.json").read_bytes()).hexdigest(),
            "new_runtime_api": [],
            "validated_interfaces": ["ContextSlot.empty", "ContextSlot.read", "ContextSlot.consume", "Certified.consume"],
            "samples": 96, "alternating_pairs": 4, "native_gate_admissions_added": 8,
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["Benchmarks/ContextSlotScale.lean", "Benchmarks/ContextSlotStudy.py"]},
            "scope": "Synthetic local native warm built-data cache versus uncached dependencies, matched independent checksums and policy oracle; setup/query separately recorded",
            "limits": ["Reference already shares Pa; external cache or redundant builds not established", "Cheap all-miss regression retained; all-miss heavy workloads show no substantial benefit", "No Euler runtime, allocation, net lines or maintenance savings; migrations 0"]},
        "context_pullback": {
            "reference_audit": context_reindex(reference),
            "local_api": ["ContextSlot.readAlong", "ContextSlot.readAlong_value", "ContextSlot.readAlong_hit", "ContextSlot.consumeAlong", "ContextSlot.consumeAlong_value", "ContextSlot.consumeAlong_reindex"],
            "tests": {"cases": 192, "reads": 729, "hits": 324, "misses": 405, "outer_equality_required": False, "outer_function_field": True, "dependent_output_and_factory_reindex_parity": True, "varying_dependency_factorization_counterexample": True, "axiom_reports": 4},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["LeanPoo/Functional/ContextPullback.lean", "Tests/FunctionalContextPullback.lean"]},
            "mechanism": "Read fixed base certified factories at an explicit projection of the outer request, using executable equality only on complete base context; constructor uses full outer context every time",
            "cost": "Execute projection once per read, compare base context, keep one base tuple; missed base builds remain. No outer equality or outer-context storage is needed in the slot",
            "limits": ["All dependency variation must be in base context or fixed captured factory inputs; arbitrary outer-dependent factories are not accepted", "Reference full-context factoring into a small comparable base is not demonstrated; N/k alone do not suffice when other inputs vary", "No automatic dependency inference or native time/allocation benchmark; Euler migrations 0; net lines and maintenance savings unmeasured"]},
        "context_observation": {
            "reference_audit": context_observation_audit(reference),
            "local_api": ["Snapshot.observe", "Snapshot.observe_val", "ContextSlot.observe", "ContextSlot.observe_empty", "ContextSlot.observe_retained", "ContextSlot.observe_hit", "ContextSlot.observe_consume", "ContextSlot.replaceObservedPublic", "ContextSlot.replaceObservedPublic_consume"],
            "tests": {"cases": 1536, "replacements": 375, "contexts": 3, "reads": 6750, "hits": 3375, "joint_candidates": 8, "joint_replacements": 1, "axiom_reports": 6, "visible_change_rejected": True, "hidden_type_and_wrong_context_rejected": True},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["LeanPoo/Functional/ContextObservation.lean", "Tests/FunctionalContextObservation.lean"]},
            "mechanism": "Observation functions map retained data now; compatible replacement retains the public cache via erased factory equality; hidden replacement values are not reconstructed; future misses use replacement public factories",
            "cost": "Traverse and allocate observed tuple, plus observation function costs; original cache may remain retained. Output constructor executes every call",
            "limits": ["Explicit total observation, public consequence and pointwise factory equivalence required", "No automatic invalidation, hidden data transport, or identity/mutation guarantee", "No new native time/allocation benchmark; Euler migrations 0; net lines and maintenance savings unmeasured"]},
        "context_view": {
            "reference_audit": context_view_audit(reference),
            "local_api": ["Snapshot.project", "Snapshot.project_val", "ContextSlot.project", "ContextSlot.project_empty", "ContextSlot.project_retained", "ContextSlot.project_hit", "ContextSlot.project_consume"],
            "tests": {"cases": 4608, "successful_preparations": 1944, "contexts": 3, "reads": 29160, "hits": 11664, "joint_consumers": 3, "duplicate_first_occurrence": True, "axiom_reports": 5},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["LeanPoo/Functional/ContextView.lean", "Tests/FunctionalContextView.lean"]},
            "mechanism": "Project retained built values and derive a narrow joint proof, retain exact context hit; empty remains empty; missing keys cannot be supplied; constructor still runs",
            "cost": "Named source scans and new projected tuple allocation, including repeated requested keys. No factory application during projection. Original broad cache may remain externally retained",
            "limits": ["Logical consequence supplied by caller, no analytical proof synthesis", "Not open recursive object projection or mutable dependency tracking", "No native time/allocation benchmark or Euler migration; net lines and maintenance savings unmeasured"]},
        "context_slot": {
            "reference_audit": context_slot_audit(reference),
            "local_api": ["Snapshot", "ContextSlot", "ContextSlot.empty", "ContextSlot.read", "ContextSlot.read_hit", "ContextSlot.read_miss", "ContextSlot.read_value", "ContextSlot.consume", "ContextSlot.consume_value", "ContextSlot.rebind", "ContextSlot.rebind_consume"],
            "mechanism": "Retain zero or one exact context/aligned built tuple/joint proof for one certified factory family; hit skips whole dependency build, miss builds and replaces previous pair; constructor still runs",
            "tests": {"cases": 192, "reads": 1215, "hits": 405, "misses": 810, "traces": 4, "rebind_hit": 1, "replacement_misses": 2, "axiom_reports": 5, "wrong_context_and_family_rejected": True},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["LeanPoo/Functional/ContextSlot.lean", "Tests/FunctionalContextSlot.lean"]},
            "cost": "Context equality, retained context and whole tuple memory; miss allocation and factory applications; constructor executes every time. One-pair bound per cache value, not across externally retained immutable histories",
            "limits": ["No output/action memoization or automatic dependency invalidation", "Family changes require explicit exact factory equality or fresh empty slot", "Complete context equality is user supplied; comparisons may be expensive", "Source Pa sharing already present; no external speedup or redundant computation established", "Reference only; migrations 0; code/maintenance/native timing/allocation savings unmeasured"]},
        "certified_consumer": {
            "reference_audit": certified_consumer_audit(reference),
            "local_api": ["Certified.consume", "Certified.consume_apply", "Certified.consume_congr", "Certified.consume_observed", "prepareConsumer", "prepareConsumer_error_iff"],
            "mechanism": "Compile an explicit constructor receiving the complete built dependency data and its joint proof into a context-indexed result factory; outputs may contain Type data and Prop fields",
            "reuse": "Equal prepared tuples preserve consumers regardless of proof choices; explicit public observation equivalence preserves arbitrary proof-aware public consumers across representations",
            "tests": {"cases": 192, "successful": 81, "output_masks": 8, "typed_outputs": 3, "contexts": 3, "axiom_reports": 4, "wrong_context_rejected": True, "invalid_joint_budget_excluded": True, "prop_only_witness_extraction_rejected": True},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["LeanPoo/Functional/CertifiedConsumer.lean", "Tests/FunctionalCertifiedConsumer.lean"]},
            "cost": "One whole dependency build in the wrapper per application; factory bodies and constructor run on every application; duplicate requested positions remain; no context memoization. Proofs erase, output data and user computation remain",
            "limits": ["Constructor and analytic joint admission explicit; no executable Type witness extraction from a Prop-only existential", "Missing dependency outcomes handled before consumption, not silently recovered", "No automatic synthesis of source witness constructions", "Public replacement requires explicit compatibility and excludes hidden-field consumers", "Reference only; migrations 0, net code/maintenance/native timing/allocation savings unmeasured"]},
        "certified_observation": {
            "reference_audit": certified_observation_audit(reference),
            "local_api": ["observeResults", "observeResults_id", "build_observe", "Certified.observe", "Certified.observe_factories", "Certified.replaceObserved", "Certified.replaceObserved_factories", "Certified.replaceObserved_public"],
            "mechanism": "Derive a certified public joint Claim from original data, or retain an existing observation-indexed joint Claim across explicitly pointwise compatible different internal types; entire certified public interface equality",
            "tests": {"cases": 1536, "replacements": 375, "joint_candidates": 8, "joint_replacements": 1, "contexts": 3, "axiom_reports": 7, "visible_change_rejected": True, "separate_availability_and_first_errors": True},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["LeanPoo/Functional/CertifiedObservation.lean", "Tests/FunctionalCertifiedObservation.lean"]},
            "cost": "Observed factories allocate wrappers and run supplied observation functions on each build; built-result observation executes observation functions and constructs a tuple. Proofs erase; candidate availability is separate",
            "limits": ["Explicit compatibility and public analytic implication required", "Old joint Claim must depend only on public observation; hidden-field contracts excluded", "Context/key/public result types fixed", "No automatic path/field/type transport or open-recursion inference", "Reference only; actual Euler migrations 0; code/maintenance/native timing/allocation savings unmeasured"]},
        "result_view": {
            "reference_audit": built_result_audit(reference),
            "local_api": ["resultAt", "resultAt_build", "projectResults", "projectEvidence", "projectEvidence_val", "build_project", "Certified.projectData", "Certified.projectData_factories", "Certified.projectData_build"],
            "mechanism": "Named dependent result access and proof-bearing projection of already built data; data-level analytic consequences avoid client factory tuple destructuring; exact projection/build commutation",
            "duplicates": "First source occurrence even for arbitrary inconsistent duplicate tuples; requested order and repeats preserved",
            "tests": {"cases": 4608, "successes": 1944, "contexts": 3, "axiom_reports": 5, "different_duplicate_values": [11, 99], "wrong_context_rejected": True},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["LeanPoo/Functional/ResultView.lean", "Tests/FunctionalResultView.lean"]},
            "cost": "Named reads scan source; result projection scans source per requested key and constructs a tuple. Building broad first computes all its factories; building projected factories computes only requested ones, including repeats. Value commutation is not cost equality",
            "limits": ["Analytic implication and inclusion remain explicit", "No changed-context transport or inference", "Already built data avoids factory reapplication only on this local projection path", "Reference already uses named structures; no claim of external duplicate computation", "No external integration; actual Euler migrations 0; code/maintenance/native timing/allocation savings unmeasured"]},
        "certified_view": {
            "reference_audit": narrow_consumer_audit(reference),
            "local_api": ["Certified.project", "Certified.project_factories", "CachedPreparation.narrow", "CachedPreparation.narrow_of_ok", "CachedPreparation.narrow_eq"],
            "success": "Project retained functions and derive the consumer Claim explicitly; no provider lookup, factory execution, or preparation",
            "failure": "Prepare the narrower keys independently with fresh admission; broad first error may be absent or reordered in the consumer interface",
            "tests": {"availability_masks": 8, "requests": 24, "duplicate_successes": 4, "rescued_broad_failures": 3, "contexts": 3, "axiom_reports": 3},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in ["LeanPoo/Functional/CertifiedView.lean", "Tests/FunctionalCertifiedView.lean"]},
            "cost": "Shared library/test additions are costs; successful projection scans the retained list for each requested key; allocate/project once before repeated builds; failed broad cache performs narrow preparation",
            "limits": ["Explicit analytic consequence and fallback admission required", "Fixed context/result types; no automatic transport or dependency inference", "Closed provider tuple, not open recursive object invalidation", "No native timing or allocation claim", "Actual Euler migrations 0; net code and maintenance savings unmeasured"]},
        "consumer_revision": {
            "time_transport_audit": consumer_time_audit(reference),
            "reference_seam": "PacketInitializedResidualEquation:45-64 uses explicit changeTime hTime for both velocity/derivative and derivative proof. Provider cache alignment is distinct from transporting these dependent types",
            "local_api": ["Prepared", "Prepared.certify", "Prepared.certify_forget", "CachedPreparation.rebind", "CachedPreparation.rebind_outcome", "ConsumerRevision.reused", "ConsumerRevision.fresh", "ConsumerRevision.registry", "ConsumerRevision.forget", "ConsumerRevision.certify", "ConsumerRevision.certify_forget", "applyTransactionCached", "applyTransactionCached_registry", "applyTransactionCached_forget", "applyTransactionCached_ofRegistry"],
            "publication": "Always full immutable patchTransaction; unrequested and nonancestor edits remain in the returned registry, no updated prefix on unknown name errors",
            "negative_scope": "Automatically rebind exact old cached outcome/certificate to the new registry through preparation equality; no client per-name/key alignment or fresh joint proof",
            "positive_scope": "Prepare fresh data once. Prepared.certify attaches supplied new analytic admission to that saved outcome without preparing again",
            "fixed_parameters": ["graph/root/order", "key list", "Context", "Value family", "joint Claim"],
            "tests": {"first_transactions": 4096, "second_transactions": 3072,
                      "negative": 2304, "positive": 1792, "first_name_errors": 1024,
                      "contexts": 2, "axiom_reports": 6, "forced_collisions": True,
                      "nonconsumer_publication_checked": True,
                      "runtime_claim": "True isolates revision plumbing; generic kernel theorems cover arbitrary joint Claims"},
            "shared_lines": 164, "fixture_lines": 203,
            "gate": {"independent_atoms": 124, "diagnostics": 4, "native_admissions": 32, "ci_jobs": 16},
            "limits": ["Full update construction still costs on negative scope; earlier view-only microbench is not a publication benchmark", "Fresh analytic admission still required; no automatic dependency inference", "Dependent time/context/result family changes need explicit transport/reindex, not mere provider rebind", "No external adapter/build/integration; actual Euler migrations 0", "Runtime/allocated-byte/peak-memory publication gains and code/maintenance savings unmeasured"]},
        "prepared_certificate_reuse": {
            "reference_seam": "Hash-bound joint_certificate_audit sources and observation_bridge: pressure-dependent equation uses explicit correction-data equality; no automatic analytic change footprint",
            "local_api": ["CachedPreparation", "cacheCertified", "TransactionPreparation.reused", "TransactionPreparation.fresh", "TransactionPreparation.forget", "prepareTransactionCached", "prepareTransactionCached_forget", "prepareTransactionCached_ofRegistry", "prepareTransactionCached_unaffected", "prepareTransactionCached_affected"],
            "alignment": "Cached certified success/first-key error is proof-bound to the exact original prepared provider. Graph/root/keys/context/result family remain fixed",
            "negative_scope": "Check every transaction name, then return the same prepared tuple/error and joint proof without provider lookup, preparation or update construction",
            "positive_scope": "Full transaction update and fresh data preparation; old joint certificate not reused, caller must supply a new analytic admission proof. Overlap does not imply the old claim is false",
            "tests": {"cases": 4096, "negative": 2304, "positive": 1792, "name_errors": 1024,
                      "contexts": 2, "axiom_reports": 4, "hash_collisions": True,
                      "wrong_provider_and_uncertified_data_rejected": True},
            "native": {"receipt": "cached-preparation-native-2026-10-05.json", "samples": 80,
                       "alternating_pairs_per_workload": 4, "requests": [8, 512],
                       "admission_cases": 10, "all_gate_native_cases": 32, "ci_jobs": 16,
                       "scope": "Both paths materialize the same initial certified tuple/key index in IO before query timing; setup reported separately; not a one-use migration comparison"},
            "limits": ["Closed functional providers, not automatic open-recursion/object invalidation", "Consumer view only, not updated registry publication", "Raw histories and name preflight still scan", "Factory bodies still run at each build", "Retained tuple and indexes cost memory; allocations/peak memory unmeasured", "No external adapter/build, actual Euler migrations 0, maintenance/code savings unmeasured"]},
        "joint_certificate_audit": joint_certificate_audit(reference),
        "observation_bridge": observation_bridge(reference),
        "evidence_transport": {
            "reference_file": "Euler/PacketInitializedResidualEquation.lean",
            "data_equality_line": 101, "dependent_certificate_line": 114,
            "equality_rewrite_line": 127,
            "local_api": ["Factory.transport", "Factory.transportProof",
                          "Factory.transport_refl", "Factory.transport_trans", "Factory.transport_roundtrip"],
            "scope": "Retarget an explicitly data-indexed witness or proposition at the same context, given equality of the entire indexed datum",
            "analytic_equivalence_inferred": False,
            "euler_adapter_implemented": False,
        },
        "context_reindex": context_reindex(reference),
        "declaration_presentation": {
            "local_api": ["Graph.SameLookup", "Graph.sameLookup_of_perm", "GraphTrace.represent",
                          "VerifiedOrder.represent", "VerifiedOrder.permute", "VerifiedOrder.permute_unique",
                          "linearizeChecked_permute_ok", "assemble_permute", "Requirements.prepare_permute"],
            "scope": "Outer declaration-list permutation under unique names; exact successful checked outputs and retained provider/checklist functions",
            "premises": ["Exact original node declarations including parent-row order and suffix flags",
                         "Global node-name uniqueness", "Same named provider dictionary and capability families"],
            "local_test": {"file": "Tests/C4Presentation.lean", "families": 64,
                           "permutations_per_family": 24, "permutation_runs": 1536,
                           "accepted_runs": 1008, "retained_pair_queries": 25200,
                           "dependent_value_contexts": 2,
                           "counts_origin": "Passing local Lean test output; the inventory script does not execute Lean"},
            "added_physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                                     ["LeanPoo/C4/Presentation.lean", "LeanPoo/Functional/Presentation.lean",
                                      "Tests/C4Presentation.lean"]},
            "negative_results": ["First missing-reference validation error can change under permutation",
                                 "Duplicate node names can change first-declaration lookup"],
            "error_payload_invariance": False, "arbitrary_graph_isomorphism_proved": False,
            "euler_registry_implemented": False, "external_lean_compilation": False,
            "runtime_benchmark": False,
        },
        "relabeling_composition": {
            "local_api": ["Graph.Relabeling", "Graph.Relabeling.trans", "Graph.Relabeling.unique",
                          "VerifiedOrder.relabel", "VerifiedOrder.relabel_unique",
                          "VerifiedOrder.relabel_trans_output", "VerifiedOrder.relabel_precedes",
                          "assemble_relabel", "Requirements.prepare_relabel"],
            "scope": "Explicit injective label map plus exact declaration permutation; compose witnesses before retained-order migration",
            "premises": ["Global injectivity of each name map", "Exact mapped node declarations and local parent rows/flags",
                         "Global source name uniqueness", "Provider alignment on original ancestors and requested keys"],
            "local_test": {"file": "Tests/C4Relabeling.lean", "families": 64, "cases": 1536,
                           "stages_per_case": 2, "independent_target_compilations": 3072,
                           "successful_cases": 1008, "mapped_pair_queries": 25200,
                           "dependent_value_contexts": 2,
                           "counts_origin": "Passing local Lean test output; this source inventory does not execute Lean"},
            "added_physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                                     ["LeanPoo/C4/Relabeling.lean", "LeanPoo/Functional/Relabeling.lean",
                                      "Tests/C4Relabeling.lean"]},
            "output_map_passes": {"composed_direct": 1, "two_sequential_migrations": 2,
                                  "basis": "Definitions and generic output-composition theorem, not a timing benchmark"},
            "negative_result": "Renaming graph labels without aligned provider names loses an existing capability",
            "arbitrary_finite_isomorphism_proved": False, "general_rejection_equivalence_proved": False,
            "error_payload_invariance": False, "euler_registry_implemented": False,
            "external_lean_compilation": False, "runtime_benchmark": False,
        },
        "provider_registry": {
            "local_api": ["ProviderRegistry.relabel", "ProviderRegistry.dictionary",
                          "ProviderRegistry.relabel_lookup", "ProviderRegistry.relabel_aligned",
                          "ProviderRegistry.relabel_missing", "assemble_relabel_registry",
                          "Requirements.prepare_relabel_registry"],
            "scope": "Construct and retain a root-specific hash registry of whole original provider functions over the verified ancestor cut; alignment for every key is proved by the library",
            "premises": ["Explicit globally injective graph relabeling witness",
                         "Global source name uniqueness for order migration",
                         "Original context, key and dependent result families"],
            "local_test": {"file": "Tests/FunctionalRegistry.lean", "order_presentations": 4,
                           "name_maps": 2, "availability_masks": 8, "key_lists": 8,
                           "registries": 64, "preparations": 512, "successful_cases": 224,
                           "dependent_value_contexts": 2, "unrelated_source_provider_excluded": True,
                           "counts_origin": "Passing local Lean test output; this inventory script does not execute Lean"},
            "local_adapter_comparison": {"baseline_file": "Tests/C4Relabeling.lean",
                                         "handwritten_mapped_name_branches": 3,
                                         "generic_registry_constructor_calls": 1,
                                         "caller_alignment_lemma_required": False,
                                         "scope": "Local fixtures only; no upstream Euler code removed or net line saving established"},
            "added_physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                                     ["LeanPoo/Functional/Registry.lean", "Tests/FunctionalRegistry.lean"]},
            "cost_boundary": ["Construct once by traversing this root's retained ancestor list and obtaining each provider function",
                              "Retain the hash table; rebuilding repeats construction work",
                              "Later dictionary accesses hash and compare strings; no worst-case constant-time or elapsed-time claim",
                              "Factory invocation retains original bodies and guards; no result memoization",
                              "Payload names are not rewritten; registry is not global or shared across roots"],
            "capability_key_enumeration_required": False, "inverse_name_map_required": False,
            "euler_registry_implemented": False, "external_lean_compilation": False,
            "runtime_benchmark": False,
        },
        "shared_provider_registry": {
            "local_api": ["ProviderRegistry.ofNames", "ProviderRegistry.ofNames_lookup",
                          "ProviderRegistry.ofNames_missing", "ProviderRegistry.ofGraph",
                          "ProviderRegistry.ofGraph_lookup", "ProviderRegistry.ofGraph_missing",
                          "assemble_ofGraph_registry", "Requirements.prepare_ofGraph_registry",
                          "ProviderRegistry.relabelGraph", "ProviderRegistry.relabelGraph_lookup",
                          "ProviderRegistry.relabelGraph_missing", "ProviderRegistry.relabelGraph_relabel",
                          "assemble_relabelGraph_registry", "Requirements.prepare_relabelGraph_registry"],
            "scope": "One declaration-wide original or explicitly mapped table shared across any verified roots of the same graph and provider families",
            "unchanged_graph_new_uniqueness_premise": False,
            "migrated_graph_premises": ["Explicit globally injective relabeling", "Exact mapped declaration permutation",
                                        "Global source name uniqueness for verified-order migration"],
            "local_test": {"file": "Tests/FunctionalSharedRegistry.lean", "order_presentations": 4,
                           "availability_masks": 8, "roots": 2, "key_lists": 9,
                           "mapped_name_maps": 2, "shared_registries": 96, "preparations": 1728,
                           "successful_cases": 624, "dependent_value_contexts": 2,
                           "declared_unrelated_provider_retained": True,
                           "unrelated_provider_cannot_fill_root_capability": True,
                           "undeclared_provider_excluded": True,
                           "standard_axiom_reports": 9,
                           "counts_origin": "Passing local Lean test output; this inventory script does not execute Lean"},
            "construction_visit_comparison": {"fixture_declarations": 5, "summed_root_ancestor_entries": 6,
                                              "root_cut_constructions": 2, "shared_constructions": 1,
                                              "criterion": "Whole-graph visits are fewer only if declaration count is below the sum of selected roots' ancestor counts",
                                              "scope": "Definition-level local setup counts; not a runtime, source-reduction or Euler maintenance measurement"},
            "physical_source_cost": {"registry_scope_helper_net_added_lines": 18,
                                     "current_registry_module_lines": len((ROOT / "LeanPoo/Functional/Registry.lean").read_text().splitlines()),
                                     "new_files": {p: len((ROOT / p).read_text().splitlines()) for p in
                                                   ["LeanPoo/Functional/SharedRegistry.lean", "Tests/FunctionalSharedRegistry.lean"]}},
            "cost_boundary": ["Traverse all graph declarations, allocate a name list and retain one hash table",
                              "Unrelated declared entries are directly queryable but root selection still uses only its verified order",
                              "Unused declarations can outweigh root overlap; no unconditional performance benefit",
                              "Obtain provider functions without factory invocation or result memoization",
                              "Original contexts, keys, dependent result families and payload names remain unchanged"],
            "graph_validation_by_registry": False, "euler_registry_implemented": False,
            "external_lean_compilation": False, "runtime_benchmark": False,
        },
        "registry_patch": {
            "local_api": ["Provider.patchKey", "Provider.patchKey_at", "Provider.patchKey_other",
                          "ProviderRegistry.patch", "ProviderRegistry.patch_missing", "ProviderRegistry.patch_at",
                          "ProviderRegistry.patch_other", "ProviderRegistry.patch_scope", "assemble_patch_stable",
                          "Requirements.prepare_patch_stable", "Requirements.mayAffect", "Requirements.mayAffect_iff",
                          "Requirements.prepare_patch_of_unaffected"],
            "scope": "One typed capability edit at an existing registry name; negative ancestry/requested-key impact supplies exact preparation equality across all contexts",
            "premises": ["Decidable equality of capability keys", "Successful known-name patch",
                         "Unchanged graph, verified order and context/key/result families",
                         "Replacement factory inhabits the original dependent result contract"],
            "local_test": {"file": "Tests/FunctionalRegistryPatch.lean", "order_presentations": 4,
                           "availability_masks": 8, "provider_names": 5, "keys": 3, "patch_modes": 2,
                           "roots": 2, "key_lists": 8, "patches": 960, "queries": 15360,
                           "negative_queries": 10752, "candidate_queries": 4608,
                           "sampled_value_or_error_changes": 1384, "unknown_name_errors": 192,
                           "contexts": 2, "retained_ancestry_indexes": 8, "standard_axiom_reports": 8,
                           "counts_origin": "Passing local Lean test output; this inventory script does not execute Lean",
                           "sample_limit": "Observed changes at contexts 0 and 7 are not a complete function-change or external fanout count"},
            "added_physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                                     ["LeanPoo/Functional/RegistryPatch.lean", "Tests/FunctionalRegistryPatch.lean"]},
            "patch_operation_counts": {"name_lookups": 1, "successful_insertions": 1,
                                       "explicit_declaration_folds": 0, "factory_invocations": 0,
                                       "scope": "Definitions only; persistent hash storage can still copy under sharing"},
            "negative_result": "A true candidate-impact query can leave selection unchanged because a more specific provider shadows the edited cell",
            "cost_boundary": ["Retain ancestry indexes once; candidate queries hash a name and scan the requested key list",
                              "Typed edits require key equality; repeated edits can accumulate provider-wrapper chains",
                              "Old registry snapshots remain usable, with possible hash storage copies",
                              "Negative impact preserves exact functions and first errors without re-preparing consumers",
                              "True impact is conservative; precise dependency closure and analytic equivalence require separate evidence"],
            "precise_dependency_closure": False, "wrapper_compaction": False,
            "euler_consumer_scopes_implemented": False, "external_lean_compilation": False,
            "runtime_benchmark": False,
        },
        "registry_rollback": {
            "local_api": ["Provider.patchKey_restore", "Provider.patchKey_overwrite", "Provider.patchKey_commute",
                          "ProviderRegistry.patch_restore_exists", "ProviderRegistry.patch_restore",
                          "Requirements.prepare_patch_restore"],
            "scope": "Dependent provider edit algebra and immediate original-cell rollback; exact dictionary and whole-preparation equality across all contexts",
            "premises": ["DecidableEq Key", "Same context/key/result families", "Successful edit and immediate restoration of saved original cell"],
            "local_test": {"rollbacks": 960, "checklist_comparisons": 15360, "contexts": 2,
                           "additional_axiom_reports": 6, "generic_arbitrary_claim_client": True,
                           "counts_origin": "Passing local Lean corpus; inventory script does not execute Lean"},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                               ["LeanPoo/Functional/RegistryPatch.lean", "Tests/FunctionalRegistryPatch.lean"]},
            "cost_boundary": ["Rollback adds a name lookup/insertion and a key-check wrapper",
                              "Retained original snapshots can cause persistent hash storage copies",
                              "Equalities support explicitly constructing normalized plans; do not compact existing closures",
                              "Intervening edits need separate proof; no general transaction rollback"],
            "automatic_batch_optimizer": False, "wrapper_compaction": False,
            "runtime_benchmark": False, "external_lean_compilation": False,
            "euler_consumer_migration": False,
        },
        "provider_overlay": {
            "local_api": ["CapabilityEdit", "ProviderOverlay.ofProvider", "ProviderOverlay.set", "ProviderOverlay.compile",
                          "ProviderOverlay.provider", "ProviderOverlay.set_provider", "ProviderOverlay.compile_provider",
                          "Requirements.prepare_overlay_set", "Requirements.prepare_overlay_compile"],
            "scope": "Unique-key typed overlay normalizes an explicit edit history over an original retained base; exact equality with sequential patching and whole preparations",
            "premises": ["DecidableEq Key", "Same context/key/dependent result families", "Explicit original base and caller-ordered typed edits"],
            "local_test": {"histories": 32, "prefix_updates": 344, "prefix_checklist_observations": 5504,
                           "final_batch_observations": 512, "contexts": 2, "standard_axiom_reports": 4,
                           "independent_last_cell_oracle": True, "generic_arbitrary_claim_client": True,
                           "counts_origin": "Passing local Lean test; inventory script does not execute Lean"},
            "structural_case": {"same_key_edits": 256, "stored_override_keys": 1,
                                "scope": "Stored entries only; not runtime timing, allocated bytes or external source savings"},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                               ["LeanPoo/Functional/Overlay.lean", "Tests/FunctionalOverlay.lean"]},
            "cost_boundary": ["Each set filters current unique override list and allocates a new list",
                              "All-distinct compilation can require quadratic scans",
                              "Query scans current distinct override keys and then may delegate to retained base",
                              "Existing base wrappers are not compacted; retain original base and compiled result",
                              "Explicit removal differs from absent override; no factory invocation during compilation"],
            "explicit_edit_history_normalization": True, "arbitrary_base_closure_compaction": False,
            "runtime_benchmark": False, "external_lean_compilation": False, "euler_consumer_migration": False,
        },
        "registry_batch": {
            "local_api": ["ProviderRegistry.patchBatch", "ProviderRegistry.patchBatch_missing", "ProviderRegistry.patchBatch_at",
                          "ProviderRegistry.patchBatch_dictionary", "ProviderRegistry.patchBatch_nil", "ProviderRegistry.patchBatch_other",
                          "ProviderRegistry.patchBatch_scope", "ProviderRegistry.patchBatch_untouched", "Requirements.batchMayAffect",
                          "Requirements.batchMayAffect_iff", "Requirements.prepare_patchBatch_stable", "Requirements.prepare_patchBatch_of_unaffected"],
            "scope": "One known-name normalized typed batch; exact sequential provider/dictionary semantics and whole-consumer negative impact preservation",
            "premises": ["DecidableEq Key", "Successful known-name batch", "Unchanged graph/order/context/key/result families", "Caller-declared consumer keys"],
            "local_test": {"graph_presentations": 4, "availability_masks": 8, "provider_names": 5, "batch_recipes": 6,
                           "roots": 2, "key_lists": 8, "batches": 960, "queries": 15360, "negative_queries": 10368,
                           "candidate_queries": 4992, "unknown_name_errors": 192, "contexts": 2, "standard_axiom_reports": 10,
                           "longest_batch": 256, "independent_last_cell_oracle": True, "generic_arbitrary_claim_client": True,
                           "counts_origin": "Passing local Lean corpus; inventory script does not execute Lean"},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                               ["LeanPoo/Functional/RegistryBatch.lean", "Tests/FunctionalRegistryBatch.lean"]},
            "structural_operation_case": {"same_key_edits": 256, "repeated_patch_name_lookups": 256,
                                          "repeated_patch_insertions": 256, "batch_name_lookups": 1, "batch_insertions": 1,
                                          "explicit_graph_folds": 0, "factory_invocations": 0,
                                          "scope": "Definitions only; excludes normalization/list allocations, hash storage copies and factory bodies"},
            "cost_boundary": ["Normalization filters current override lists; all-distinct batches can be quadratic",
                              "Impact scans explicit edit history and requested key list after ancestry query",
                              "One persistent hash insertion can copy shared storage",
                              "Repeated batches can retain prior provider/base overlay layers; no arbitrary closure compaction",
                              "Empty known-name batch preserves functions, unknown name still fails; no general multi-name transaction"],
            "runtime_benchmark": False, "precise_dependency_closure": False,
            "euler_consumer_migration": False, "external_lean_compilation": False,
        },
        "registry_transaction": {
            "local_api": ["RegistryEdit", "ProviderRegistry.patchTransaction", "ProviderRegistry.patchTransaction_nil",
                          "ProviderRegistry.patchTransaction_cons", "ProviderRegistry.patchTransaction_missing",
                          "ProviderRegistry.patchTransaction_scope", "Requirements.transactionMayAffect",
                          "Requirements.transactionMayAffect_iff", "Requirements.prepare_patchTransaction_of_unaffected"],
            "scope": "Caller-ordered multi-name pure transaction; first unknown-name error exposes no partial registry; whole-consumer negative scope reuse",
            "premises": ["DecidableEq Key", "Successful transaction", "Fixed graph/order/context/key/result families", "Explicit consumer keys"],
            "local_test": {"presentations": 4, "masks": 8, "plans": 8, "roots": 2, "key_lists": 8,
                           "successes": 192, "first_unknown_errors": 64, "queries": 3072, "negative_queries": 1920, "contexts": 2,
                           "standard_axiom_reports": 6, "independent_scalar_oracle": True,
                           "generic_arbitrary_claim_client": True, "failure_after_valid_prefix": True,
                           "counts_origin": "Passing Lean corpus; inventory script does not execute Lean"},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                               ["LeanPoo/Functional/RegistryTransaction.lean", "Tests/FunctionalRegistryTransaction.lean"]},
            "cost_boundary": ["One lookup per reached named batch and one insertion per successful batch",
                              "Stops at first unknown name; valid prefix work still costs CPU/allocation",
                              "Repeated names are not grouped; prior base-overlay layers can accumulate",
                              "Impact scans named batches and explicit key histories; no precise dependency inference",
                              "Return-value atomicity only; no external effects, concurrency transaction or storage identity claim"],
            "runtime_benchmark": False, "euler_consumer_migration": False, "external_lean_compilation": False,
        },
        "indexed_overlay": {
            "local_api": ["IndexedOverlay.ofProvider", "IndexedOverlay.provider", "IndexedOverlay.set",
                          "IndexedOverlay.extend", "IndexedOverlay.compile", "IndexedOverlay.set_provider",
                          "IndexedOverlay.extend_base", "IndexedOverlay.extend_provider", "IndexedOverlay.extend_append",
                          "IndexedOverlay.compile_provider", "Requirements.prepare_indexed_extend", "Requirements.prepare_indexed_compile"],
            "scope": "Retained dependent hash overrides; exact list-overlay/sequential function and whole-preparation equality; original base preserved across extensions",
            "premises": ["BEq Key", "Hashable Key", "LawfulBEq Key", "DecidableEq Key", "Fixed context/key/result families", "Retain overlay state between updates"],
            "local_test": {"histories": 32, "prefix_updates": 344, "prefix_observations": 5504,
                           "batch_observations": 512, "retained_snapshot_observations": 5504, "contexts": 2,
                           "all_keys_hash_collide": True, "same_key_history": 256, "stored_overrides": 1,
                           "standard_axiom_reports": 9, "generic_arbitrary_claim_client": True,
                           "counts_origin": "Passing Lean corpus; inventory script does not execute Lean"},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                               ["LeanPoo/Functional/IndexedOverlay.lean", "Tests/FunctionalIndexedOverlay.lean"]},
            "cost_boundary": ["Hash insertion/query replace full override-list filtering/scanning; no unconditional constant-time claim",
                              "Hash collisions, resizing and shared persistent storage copies retain costs",
                              "Dependent hash payload stores original typed functions without invoking factories",
                              "Original base retained when state is extended; already wrapped input base is not compacted",
                              "Small tables may not benefit; key hashes/equality and adapter costs matter"],
            "runtime_benchmark_receipt": "Benchmarks/receipts/indexed-overlay-2026-10-05.json",
            "runtime_scope": "Paired local interpreter workloads only; not whole preparation/graph/Euler proof speedup",
            "euler_consumer_migration": False, "external_lean_compilation": False,
        },
        "indexed_registry": {
            "local_api": ["IndexedRegistry.ofRegistry", "IndexedRegistry.dictionary", "IndexedRegistry.snapshot",
                          "IndexedRegistry.patchBatch", "IndexedRegistry.ofRegistry_dictionary", "IndexedRegistry.snapshot_dictionary",
                          "IndexedRegistry.patchBatch_missing", "IndexedRegistry.patchBatch_at", "IndexedRegistry.patchBatch_other",
                          "IndexedRegistry.patchBatch_base", "IndexedRegistry.patchBatch_scope", "IndexedRegistry.patchBatch_agreement",
                          "Requirements.prepare_indexedRegistry_of_unaffected"],
            "scope": "Per-name indexed state retained across batches; exact dictionary/consumer agreement with ordinary batches and original-base retention",
            "premises": ["Lawful BEq, Hashable and DecidableEq Key", "Known provider for successful update", "Fixed graph/order/context/key/result families", "Explicit consumer read scopes"],
            "local_test": {"presentations": 4, "availability_masks": 8, "plans": 8, "roots": 2,
                           "key_lists": 8, "batches": 352, "unknown_name_errors": 64, "queries": 5632,
                           "negative_queries": 3136, "contexts": 2, "standard_axiom_reports": 9,
                           "all_capability_hashes_collide": True, "independent_scalar_oracle": True,
                           "generic_arbitrary_claim_client": True, "retained_bases_and_snapshots": True,
                           "counts_origin": "Passing Lean corpus; inventory script does not execute Lean"},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                               ["LeanPoo/Functional/IndexedRegistry.lean", "Tests/FunctionalIndexedRegistry.lean"]},
            "cost_boundary": ["Initial conversion maps all entries once; no factory invocation",
                              "Successful batch performs one name lookup/insertion and indexed cell writes, retaining original base",
                              "Dictionary queries do not materialize registry or reconstruct declarations",
                              "Snapshot maps the full table; use only when concrete ProviderRegistry is required",
                              "Collisions/resizing/persistent copies/base costs and small-table overhead remain",
                              "Individual batches expose successful prefixes; IndexedTransaction separately supplies pure atomic multi-name updates"],
            "runtime_benchmark_receipt": "Benchmarks/receipts/indexed-registry-2026-10-05.json",
            "runtime_scope": "Paired selected named-batch interpreter updates and direct queries only",
            "euler_consumer_migration": False, "external_lean_compilation": False,
        },
        "indexed_transaction": {
            "local_api": ["IndexedRegistry.patchTransaction", "IndexedRegistry.patchTransaction_nil",
                          "IndexedRegistry.patchTransaction_cons", "IndexedRegistry.patchTransaction_missing",
                          "IndexedRegistry.patchTransaction_base", "IndexedRegistry.patchTransaction_scope",
                          "Requirements.prepare_indexedTransaction_of_unaffected",
                          "IndexedRegistry.patchTransaction_congr", "IndexedRegistry.ofRegistry_patchTransaction",
                          "IndexedRegistry.ofRegistry_transaction_consumer"],
            "reused_api": ["RegistryEdit", "Requirements.transactionMayAffect"],
            "premises": ["Lawful BEq, Hashable and DecidableEq Key for consumer equality",
                         "Fixed graph/order/context/key/result families", "Successful transaction and negative read scope"],
            "local_test": {"successful_transactions": 192, "first_unknown_errors": 64,
                           "queries": 3072, "negative_queries": 1920, "contexts": 2,
                           "standard_axiom_reports": 9, "all_capability_hashes_collide": True,
                           "independent_scalar_oracle": True, "ordinary_transaction_control": True,
                           "retained_bases_and_snapshots": True, "generic_arbitrary_claim_client": True,
                           "counts_origin": "Passing Lean corpus; inventory script does not execute Lean"},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                               ["LeanPoo/Functional/IndexedTransaction.lean", "Tests/FunctionalIndexedTransaction.lean"]},
            "cost_boundary": ["Pure return-value atomicity: first unknown name returns no prefix registry",
                              "One name lookup/insertion per reached successful batch; retains original indexed bases",
                              "No full-table snapshot, graph rebuilding or factory execution in transaction path",
                              "One whole-consumer rewrite replaces caller per-batch proof chaining for negative scopes",
                              "Touched scopes still require alignment; collisions/copies/retention and scope scans remain",
                              "No new transaction timing, allocated-byte, peak-memory or Euler savings measurement"],
            "euler_consumer_migration": False, "external_lean_compilation": False,
        },
        "transaction_outcome_equivalence": {
            "local_api": ["IndexedRegistry.patchTransaction_congr", "IndexedRegistry.ofRegistry_patchTransaction",
                          "IndexedRegistry.ofRegistry_transaction_consumer"],
            "scope": "Exact complete mapped transaction outcomes across ordinary/indexed representations, including first unknown names and arbitrary dictionary consumers",
            "premises": ["Same edit list and fixed Context/Key/result family", "Lawful BEq, Hashable and DecidableEq Key",
                         "General theorem requires exact dictionaries and identical name membership",
                         "ofRegistry discharges both alignment premises; no success or negative-impact premise"],
            "local_test": {"complete_outcome_arbitrary_claim_client": True,
                           "full_dictionary_equality_empty_name_counterexample": True,
                           "empty_name_runtime_cells": 12, "new_standard_axiom_reports": 3,
                           "existing_transaction_successes": 192, "existing_first_unknown_errors": 64,
                           "ordinary_and_scalar_controls": True,
                           "counts_origin": "Passing Lean corpus; inventory script does not execute Lean"},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                               ["LeanPoo/Functional/IndexedTransaction.lean", "Tests/FunctionalIndexedTransaction.lean"]},
            "prior_physical_lines": {"LeanPoo/Functional/IndexedTransaction.lean": 101,
                                     "Tests/FunctionalIndexedTransaction.lean": 159},
            "cost_boundary": ["Three erased proof APIs; runtime transaction implementation unchanged",
                              "No per-name/key alignment or negative-impact proof needed after ofRegistry conversion",
                              "Nested consumer missing-key errors, caller context evaluation and arbitrary claims transfer exactly",
                              "This compares representations under the same edits, not old/new affected consumers",
                              "No new timing, allocation, peak-memory or external savings measurement"],
            "euler_consumer_migration": False, "external_lean_compilation": False,
        },
        "transaction_preflight": {
            "local_api": ["checkTransactionNames", "ProviderRegistry.checkTransaction", "IndexedRegistry.checkTransaction",
                          "checkTransactionNames_ok_iff", "checkTransactionNames_congr",
                          "ProviderRegistry.checkTransaction_outcome", "IndexedRegistry.checkTransaction_outcome",
                          "ProviderRegistry.checkTransaction_after", "IndexedRegistry.checkTransaction_after",
                          "IndexedRegistry.ofRegistry_checkTransaction"],
            "scope": "Optional initial-name-scope preflight with exact transaction success/first-error agreement",
            "premises": ["Immutable registry scope; all batches preserve membership",
                         "Scope agreement required to carry a cached preflight to a different registry",
                         "Success establishes registered names only, not capability availability"],
            "local_test": {"scope_masks": 16, "name_plans": 259, "batch_widths": [0, 3, 64],
                           "cases": 12432, "successes": 1056, "first_unknown_errors": 11376,
                           "cached_scope_controls": 1056, "contexts": 2, "standard_axiom_reports": 7,
                           "independent_initial_name_oracle": True, "ordinary_and_indexed_transaction_controls": True,
                           "preflight_success_with_capability_error": True, "generic_arbitrary_claim_client": True,
                           "counts_origin": "Passing Lean corpus; inventory script does not execute Lean"},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                               ["LeanPoo/Functional/TransactionCheck.lean", "Tests/FunctionalTransactionCheck.lean"]},
            "cost_boundary": ["One name membership query per reached batch, stopping at first unknown name",
                              "Does not traverse capability edit cells, invoke factories or construct update tables",
                              "Inputs/edit-list construction, hash collisions and name-scan costs remain",
                              "Running preflight then a successful transaction adds an extra name scan; optional, not default",
                              "No elapsed-time/allocation/peak-memory or external maintenance win measured"],
            "euler_consumer_migration": False, "external_lean_compilation": False,
        },
        "scoped_transaction_preparation": {
            "local_api": ["Requirements.prepareTransaction", "Requirements.prepareTransaction_eq",
                          "Requirements.prepareTransaction_ofRegistry", "Requirements.prepareTransaction_unaffected"],
            "scope": "Consumer-only preparation with complete full-transaction outcome semantics; no updated registry returned",
            "premises": ["Fixed verified graph/order, context/key/result family", "Lawful BEq, Hashable and DecidableEq Key",
                         "Conservative declared ancestor/key scope; all unknown names still checked"],
            "local_test": {"cases": 4096, "negative_scopes": 2304, "positive_scopes": 1792,
                           "first_name_errors": 1024, "contexts": 2, "standard_axiom_reports": 3,
                           "independent_scalar_oracle": True, "ordinary_and_full_indexed_controls": True,
                           "all_capability_hashes_collide": True, "generic_arbitrary_claim_client": True,
                           "counts_origin": "Passing Lean corpus; inventory script does not execute Lean"},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                               ["LeanPoo/Functional/ScopedTransaction.lean", "Tests/FunctionalScopedTransaction.lean",
                                "Benchmarks/ScopedTransactionScale.lean", "Benchmarks/ScopedTransactionStudy.py"]},
            "native_receipt": "Benchmarks/receipts/scoped-transaction-native-2026-10-05.json",
            "native_samples": 32, "alternating_pairs_per_workload": 4,
            "mandatory_native_cases": 8, "all_gate_native_cases": 32, "ci_jobs": 16,
            "cost_boundary": ["Negative scope does no update table/cell writes, but performs scope scan, name preflight and original preparation",
                              "Positive scope adds impact scan then executes full transaction",
                              "Disjoint keys still require edit-cell scans; conservative positives may be shadowed",
                              "Shared already-updated registries can amortize updates across consumers; this is not a replacement for publishing state",
                              "Measured local native consumer-only calls exclude graph/index/registration/conversion/inputs/factory bodies/oracle",
                              "No allocation/peak-memory/whole Euler/maintenance saving measurement"],
            "euler_consumer_migration": False, "external_lean_compilation": False,
        },
        "retained_key_index": {
            "local_api": ["Requirements.KeyIndex", "Requirements.KeyIndex.ofKeys", "Requirements.KeyIndex.contains",
                          "Requirements.batchMayAffectIndexed", "Requirements.transactionMayAffectIndexed",
                          "Requirements.prepareTransactionIndexed", "Requirements.KeyIndex.contains_iff",
                          "Requirements.KeyIndex.contains_eq", "Requirements.batchMayAffectIndexed_eq",
                          "Requirements.transactionMayAffectIndexed_eq", "Requirements.prepareTransactionIndexed_eq",
                          "Requirements.prepareTransactionIndexed_ofRegistry"],
            "scope": "Retained requested-key hash index, tied to exact list membership; consumer key order/duplicates and complete transaction outcomes preserved",
            "premises": ["Lawful BEq, Hashable and DecidableEq Key", "Index tied to requested list; rebuild for a different list",
                         "Conservative ancestor/key impact; raw history scans, unknown-name checks and full positive fallback retained"],
            "local_test": {"cases": 4096, "negative_scopes": 2304, "positive_scopes": 1792,
                           "first_name_errors": 1024, "contexts": 2, "standard_axiom_reports": 6,
                           "all_capability_hashes_collide": True, "membership_and_deduplication_controls": True,
                           "independent_scalar_oracle": True, "list_scoped_full_indexed_and_ordinary_controls": True,
                           "generic_arbitrary_claim_client": True,
                           "counts_origin": "Passing Lean corpus; inventory script does not execute Lean"},
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                               ["LeanPoo/Functional/KeyIndex.lean", "Tests/FunctionalKeyIndex.lean",
                                "Benchmarks/KeyIndexScale.lean", "Benchmarks/KeyIndexStudy.py"]},
            "native_receipt": "Benchmarks/receipts/key-index-native-2026-10-05.json",
            "native_samples": 80, "alternating_pairs_per_workload": 4, "request_widths": [8, 512],
            "mandatory_native_cases": 10, "all_gate_native_cases": 32, "ci_jobs": 16,
            "cost_boundary": ["Build requested-key set once; duplicates removed only for impact membership",
                              "One hash probe per reached edit cell instead of repeated requested-list scans; raw history still scanned",
                              "Collision/copy/build costs remain; no unconditional O(1) or universal switch",
                              "Construction and retained query timings separate; per-sample compile+query totals preserve one-use losses",
                              "Outside ancestry/early overlap/unknown names may gain no indexed membership work",
                              "No allocations/peak-memory/whole Euler/maintenance savings measured"],
            "euler_consumer_migration": False, "external_lean_compilation": False,
        },
        "native_registry_validation": {
            "entry_points": ["lake build indexedRegistryScale", "IndexedRegistryStudy.py --engine native/interpreter --policy latest/retained", "just _check-native-registry"],
            "new_library_api": False,
            "existing_contracts": ["IndexedRegistry.patchBatch", "IndexedRegistry.dictionary", "Requirements.prepare_indexedRegistry_of_unaffected"],
            "receipts": ["Benchmarks/receipts/indexed-registry-" + engine + "-" + policy + "-2026-10-05.json"
                         for engine in ["native", "interpreter"] for policy in ["latest", "retained"]],
            "samples": 96, "alternating_pairs_per_workload_engine_policy": 4,
            "cross_engine_current_and_snapshot_controls": True,
            "mandatory_native_cases": 4, "ci_jobs": 16,
            "physical_lines": {p: len((ROOT / p).read_text().splitlines()) for p in
                               ["Benchmarks/IndexedRegistryScale.lean", "Benchmarks/IndexedRegistryStudy.py"]},
            "cost_boundary": ["Retained query views of every pre-update state stay live across timed updates and final queries",
                              "Current cells and sampled old-snapshot cells checked by independent scalar oracle outside timers",
                              "Source/toolchain/config and native binary hashes bind selected execution receipts",
                              "Native and interpreter update conclusions can differ; no universal representation switch",
                              "Initial common registration, inputs/imports/build/oracle and graph/order/preparation/Euler proofs excluded",
                              "Allocated bytes, peak memory and external maintenance savings unmeasured"],
            "euler_consumer_migration": False, "external_lean_compilation": False,
        },
        "local_contract": {"files": {p: hashlib.sha256((ROOT / p).read_bytes()).hexdigest() for p in local},
                           "scope": "Exact factory agreement for View; pointwise public observation equality for Observation, allowing different representation types; both source preparations successful; fixed Context/Key/public observation types; explicit context projection through Reindex; unique-name declaration permutation through Presentation; composed explicit Relabeling witnesses with scoped provider alignment; constructive whole-provider alignment through a retained ancestor-cut Registry and a declaration-wide SharedRegistry for multiple verified roots; typed single-capability patch noninterference from negative ancestry/checklist impact",
                           "runtime_benchmark": False},
        "unmeasured": {"actual_euler_consumers_migrated": 0, "net_lines_saved": None,
                       "maintenance_hours_saved": None, "affected_euler_consumers_avoided": None},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reference", type=Path, default=ROOT / ".data/NavierStokesAndEuler")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = study(args.reference)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"files": result["reference"]["tracked_lean_files"],
                      "lines": result["reference"]["physical_lines"],
                      "lexical_sites": {k: sum(len(p["lines"]) for p in v)
                                        for k, v in result["lexical_mentions"].items()}}))


if __name__ == "__main__":
    main()
