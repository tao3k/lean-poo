#!/usr/bin/env python3
"""Execute the pinned POOF Definitions/Examples/Checks in source order.

The Racket reader owns Scheme parsing. Python only extracts balanced Scribble
code blocks, checks their source identity and controls the subprocess budget.
Formatting-only code:comment forms are removed as in examples-module.rkt.
eval:check/eval:error are instrumented with fail-fast assertions and receipts.
The original reference checkout is read-only and is never a runtime dependency.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SOURCE_CODE = ROOT / 'Tests/Fixtures/poof-source-v1.json'


def source_code(paper=None, fixture=SOURCE_CODE):
    """Load the reviewed source, or its versioned, independently hashed blocks."""
    expected = json.loads((ROOT / 'docs/audits/poof/requirements-v1.json').read_text())['paper_sha256']
    if paper is not None:
        digest = hashlib.sha256(paper.read_bytes()).hexdigest()
        if digest != expected:
            raise ValueError('Paper SHA256 differs from the reviewed source')
        extracted = list(blocks(paper.read_text()))
        return digest, extracted
    saved = json.loads(fixture.read_text())
    if saved['schema'] != 'lean-poo.poof-source-code.v1' or saved['paper_sha256'] != expected:
        raise ValueError('Source fixture differs from the reviewed paper identity')
    extracted = []
    previous = 0
    for block in saved['blocks']:
        if block['kind'] not in ('Definitions', 'Examples', 'Checks') or block['line'] <= previous:
            raise ValueError('Invalid source fixture block identity')
        if hashlib.sha256(block['code'].encode()).hexdigest() != block['sha256']:
            raise ValueError('Source fixture code hash differs')
        extracted.append((block['kind'], block['line'], block['code']))
        previous = block['line']
    if len(extracted) != saved['source_blocks'] or not extracted:
        raise ValueError('Source fixture block count differs')
    return expected, extracted


def compare_checks(source, rows, mapped):
    expected_lines = {check['source_line'] for check in mapped}
    if len(rows) != len(mapped) or {row['line'] for row in rows} != expected_lines:
        raise ValueError('Lean differential receipt must contain each of the 24 checks once')
    observed = {row['line']: row['canonical'] for row in rows}
    values = [check for check in source if check['kind'] == 'value']
    if len(values) != len(mapped) or {check['line'] for check in values} != expected_lines:
        raise ValueError('Source differential receipt must contain each of the 24 checks once')
    for check in values:
        if observed[check['line']] != check['canonical']:
            raise ValueError(f"Source/Lean differential mismatch at paper line {check['line']}")


def blocks(source):
    for match in re.finditer(r'@(Definitions|Examples|Checks)\[', source):
        if source[max(0, match.start() - 2):match.start()] == '@;':
            continue
        start = match.end()
        stack = [']']
        index = start
        string = False
        comment = False
        escaped = False
        block_comment = 0
        while stack and index < len(source):
            char = source[index]
            pair = source[index:index + 2]
            if block_comment:
                if pair == '#|':
                    block_comment += 1
                    index += 2
                    continue
                if pair == '|#':
                    block_comment -= 1
                    index += 2
                    continue
            elif comment:
                comment = char != '\n'
            elif string:
                if escaped:
                    escaped = False
                elif char == '\\':
                    escaped = True
                elif char == '"':
                    string = False
            elif pair == '#|':
                block_comment = 1
                index += 2
                continue
            elif char == ';':
                comment = True
            elif char == '"':
                string = True
            elif char in '([{':
                stack.append({'(': ')', '[': ']', '{': '}'}[char])
            elif char in ')]}':
                if char != stack.pop():
                    raise ValueError(f'Unbalanced source code at offset {index}')
            index += 1
        if stack:
            raise ValueError(f'Unclosed code block at offset {match.start()}')
        yield match.group(1), source.count('\n', 0, match.start()) + 1, source[start:index - 1]


PRELUDE = r'''#lang racket/base
(require racket/list json)
(define ns (make-base-namespace))
(parameterize ([current-namespace ns])
  (namespace-require 'racket)
  (namespace-require 'srfi/1)
  (eval '(require (only-in racket/base [define def])))
  (eval '(define source-line 0))
  (eval '(define source-results '()))
  (eval '(define (canonical value)
    (cond [(or (boolean? value) (string? value) (real? value)) value]
          [(and (number? value) (not (real? value)))
           (hash 'complex (list (real-part value) (imag-part value)))]
          [(symbol? value) (hash 'symbol (symbol->string value))]
          [(list? value) (map canonical value)]
          [(pair? value) (hash 'pair (list (canonical (car value)) (canonical (cdr value))))]
          [else (error 'canonical "unsupported check value: ~s" value)])))
  (eval '(define-syntax-rule (eval:check observed wanted)
    (let ([a observed] [e wanted])
      (unless (equal? a e) (error 'eval:check "line ~a: ~s != ~s" source-line a e))
      (set! source-results (cons (hash 'line source-line 'kind "value"
        'actual (format "~s" a) 'expected (format "~s" e)
        'canonical (canonical a)) source-results)) a)))
  (eval '(define-syntax-rule (eval:error actual)
    (let ([failed? (with-handlers ([exn:fail? (lambda (_) #t)]) actual #f)])
      (unless failed? (error 'eval:error "line ~a: expected an error" source-line))
      (set! source-results (cons (hash 'line source-line 'kind "error") source-results))))))
(define removed (gensym 'comment))
(define (clean value)
  (cond [(and (pair? value) (eq? (car value) 'code:comment)) removed]
        [(pair? value) (let ([first (clean (car value))] [rest (clean (cdr value))])
          (if (eq? first removed) rest (cons first rest)))]
        [else value]))
(define (run-block block)
  (define port (open-input-string (caddr block)))
  (port-count-lines! port)
  (let loop ()
    (define form (read-syntax "poof.scrbl" port))
    (unless (eof-object? form)
      (define line (+ (cadr block) (sub1 (syntax-line form))))
      (define expression (clean (syntax->datum form)))
      (unless (eq? expression removed)
        (parameterize ([current-namespace ns])
          (namespace-set-variable-value! 'source-line line)
          (with-handlers ([exn:fail? (lambda (e)
            (eprintf "POOF-SOURCE-ERROR block=~a line=~a: ~a\n" (car block) line (exn-message e))
            (raise e))])
            (call-with-values (lambda () (eval expression)) (lambda results (void))))))
      (loop))))
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--paper', type=Path)
    parser.add_argument('--source-code', type=Path, default=SOURCE_CODE)
    parser.add_argument('--write-source-code', type=Path)
    parser.add_argument('--racket', default='racket')
    parser.add_argument('--receipt', type=Path)
    parser.add_argument('--timeout', type=int, default=120)
    parser.add_argument('--compare-lean', action='store_true')
    args = parser.parse_args()
    paper = args.paper.resolve() if args.paper else None
    digest, extracted = source_code(paper, args.source_code)
    if args.write_source_code:
        if paper is None:
            parser.error('--write-source-code requires --paper')
        args.write_source_code.parent.mkdir(parents=True, exist_ok=True)
        fixture = dict(schema='lean-poo.poof-source-code.v1', paper_sha256=digest,
            source_blocks=len(extracted), blocks=[dict(kind=kind, line=line, code=body,
                sha256=hashlib.sha256(body.encode()).hexdigest()) for kind, line, body in extracted])
        args.write_source_code.write_text(json.dumps(fixture, ensure_ascii=False, indent=2) + '\n')
    forms = ['(list ' + json.dumps(kind) + ' ' + str(line) + ' ' +
             json.dumps(body, ensure_ascii=False) + ')' for kind, line, body in extracted]
    script = PRELUDE + '\n(define blocks (list\n' + '\n'.join(forms) + '))\n' + r'''
(for-each run-block blocks)
(parameterize ([current-namespace ns])
  (write-json (hash 'racket_version (version) 'checks (reverse (eval 'source-results)))))
(newline)
'''
    with tempfile.TemporaryDirectory(prefix='lean-poof-source-') as temp:
        generated = Path(temp) / 'source-check.rkt'
        generated.write_text(script)
        result = subprocess.run([args.racket, str(generated)], cwd=ROOT,
                                capture_output=True, text=True, timeout=args.timeout)
    if result.returncode:
        print(result.stderr, file=sys.stderr, end='')
        raise SystemExit(result.returncode)
    receipt = json.loads(result.stdout)
    receipt.update(schema='lean-poo.poof-source-execution.v1', paper_sha256=digest,
                   source_blocks=len(extracted), boundary='Original code blocks; fail-fast check macros; no whole-language equivalence claim')
    mapped = json.loads((ROOT / 'docs/audits/poof/checks-v1.json').read_text())['paper_checks']
    actual_lines = {check['line'] for check in receipt['checks'] if check['kind'] == 'value'}
    if not {check['source_line'] for check in mapped}.issubset(actual_lines):
        raise ValueError('Not every reviewed original check executed')
    if args.compare_lean:
        lean = subprocess.run(['lake', 'env', 'lean', 'Tests/SourceDifferential.lean'], cwd=ROOT,
                              capture_output=True, text=True, timeout=args.timeout)
        if lean.returncode:
            print(lean.stdout + lean.stderr, file=sys.stderr, end='')
            raise SystemExit(lean.returncode)
        rows = [json.loads(line.removeprefix('POOF-DIFFERENTIAL ')) for line in lean.stdout.splitlines()
                if line.startswith('POOF-DIFFERENTIAL ')]
        compare_checks(receipt['checks'], rows, mapped)
        receipt['lean_differential_checks'] = len(rows)
        receipt['adaptation_manifest_sha256'] = hashlib.sha256(
            (ROOT / 'docs/audits/poof/checks-v1.json').read_bytes()).hexdigest()
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt, ensure_ascii=False, indent=2) + '\n')
    print('POOF-SOURCE-OK ' + json.dumps({'paper_sha256': digest, 'source_blocks': len(extracted),
          'checks': len(receipt['checks']), 'mapped_checks': len(mapped), 'racket_version': receipt['racket_version'],
          'lean_differential_checks': receipt.get('lean_differential_checks', 0)}))


if __name__ == '__main__':
    main()
