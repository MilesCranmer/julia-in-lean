#!/usr/bin/env python3
"""Seed and check source-mirrored Lean comments against Git objects."""

import argparse
import re
import subprocess
import sys
from pathlib import Path, PurePosixPath

HEADER = re.compile(rb'-- Source: ([^\r\n:]+):([1-9][0-9]*)-([1-9][0-9]*) @ ([0-9a-f]{40})\n\Z')
DOC_HEADER = re.compile(rb'Julia source: ([^\r\n:]+):([1-9][0-9]*)-([1-9][0-9]*) @ ([0-9a-f]{40})\n\Z')


def source_path(value):
    path = PurePosixPath(value)
    if (path.is_absolute() or str(path) != value or any(p in ('.', '..') for p in value.split('/'))
            or path.suffix not in ('.jl', '.c', '.h') or ':' in value or '\n' in value or '\r' in value):
        raise ValueError(f'invalid source path: {value!r}')
    return path


def model_paths(root, source):
    suffix = {'.jl': '', '.c': '_c', '.h': '_h'}[source.suffix]
    relative = source.with_name(source.stem + suffix + '.lean')
    return root / 'JuliaLean' / relative, root / 'JuliaLean' / 'Proofs' / relative


def git(repo, *args):
    result = subprocess.run(['git', '-C', str(repo), *args], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if result.returncode:
        raise ValueError(result.stderr.decode('utf-8', 'replace').strip())
    return result.stdout


def revision(repo, value):
    resolved = git(repo, 'rev-parse', '--verify', '--end-of-options', value + '^{commit}').strip().decode('ascii')
    if not re.fullmatch('[0-9a-f]{40}', resolved):
        raise ValueError('revision did not resolve to a full SHA-1 commit')
    return resolved


def blob(repo, sha, source):
    data = git(repo, 'show', f'{sha}:{source}')
    data.decode('utf-8')
    return data


def lines(data):
    parts = data.split(b'\n')
    return [part + b'\n' for part in parts[:-1]] + ([parts[-1]] if parts[-1] else [])


def render(source, sha, first, last, source_lines):
    if first > last or last > len(source_lines):
        raise ValueError(f'invalid source range {first}-{last} in {source}')
    payload = b''.join(b'-- ' + line for line in source_lines[first - 1:last])
    if not payload.endswith(b'\n'):
        payload += b'\n'
    return f'-- Source: {source}:{first}-{last} @ {sha}\n'.encode() + payload + b'-- /Source\n'


def render_doc(source, sha, first, last, source_lines):
    """Source lines for a Lean docstring: a fenced block longer than any backtick run inside it.
    `-/` and `/-` would close or open a Lean comment, so they are written `-\\/` and `/\\-`."""
    if first > last or last > len(source_lines):
        raise ValueError(f'invalid source range {first}-{last} in {source}')
    body = b''.join(source_lines[first - 1:last])
    if not body.endswith(b'\n'):
        body += b'\n'
    body = body.replace(b'-/', b'-\\/').replace(b'/-', b'/\\-')
    fence = b'`' * max(3, max((len(run) for run in re.findall(rb'`+', body)), default=0) + 1)
    return f'Julia source: {source}:{first}-{last} @ {sha}\n'.encode() + fence + b'julia\n' + body + fence + b'\n'


def coverage(repo, root, target):
    """Check every source block under JuliaLean/ against Git and return the target lines it covers."""
    cache, covered, problems, count = {}, {}, [], 0

    def source_lines(sha, path):
        if (sha, path) not in cache:
            cache[sha, path] = lines(blob(repo, sha, path))
        return cache[sha, path]

    for model in sorted((root / 'JuliaLean').rglob('*.lean')):
        physical = lines(model.read_bytes())
        index = 0
        while index < len(physical):
            line = physical[index]
            match = (HEADER.fullmatch(line) if line.startswith(b'-- Source:') else
                     DOC_HEADER.fullmatch(line) if line.startswith(b'Julia source:') else None)
            if match is None:
                if line.startswith((b'-- Source:', b'Julia source:')):
                    problems.append(f'{model}:{index + 1}: malformed source header')
                index += 1
                continue
            path, first, last, sha = match.groups()
            path, first, last, sha = path.decode(), int(first), int(last), sha.decode('ascii')
            try:
                text = source_lines(sha, str(source_path(path)))
                expected = (render if line.startswith(b'-- ') else render_doc)(path, sha, first, last, text)
            except ValueError as error:
                problems.append(f'{model}:{index + 1}: {error}')
                index += 1
                continue
            size = expected.count(b'\n')
            if b''.join(physical[index:index + size]) != expected:
                problems.append(f'{model}:{index + 1}: block differs from {sha}:{path}:{first}-{last}')
                index += 1
                continue
            count += 1
            if sha == target:
                covered.setdefault(path, set()).update(range(first, last + 1))
            index += size
    return covered, problems, count


def blocks(repo, model, source):
    data = model.read_bytes()
    physical = lines(data)
    found = []
    index = 0
    while index < len(physical):
        line = physical[index]
        if line.startswith(b'-- Source:'):
            match = HEADER.fullmatch(line)
            if not match:
                raise ValueError(f'{model}:{index + 1}: malformed source header')
            path, first, last, sha = match.groups()
            if path.decode('utf-8') != str(source):
                raise ValueError(f'{model}:{index + 1}: source does not match requested path')
            first, last, sha = int(first), int(last), sha.decode('ascii')
            if revision(repo, sha) != sha:
                raise ValueError(f'{model}:{index + 1}: invalid commit')
            original = blob(repo, sha, source)
            expected = render(source, sha, first, last, lines(original))
            count = last - first + 3
            actual = b''.join(physical[index:index + count])
            if actual != expected:
                raise ValueError(f'{model}:{index + 1}: source block differs from {sha}:{source}:{first}-{last}')
            untranslated = index > 0 and physical[index - 1] == b'-- UNTRANSLATED\n'
            found.append((sha, first, last, original, untranslated))
            index += count
        else:
            index += 1
    if not found:
        raise ValueError(f'{model}: no source blocks')
    return found


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parent.parent.parent / 'julia')
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent.parent)
    sub = parser.add_subparsers(dest='command', required=True)
    for name in ('seed', 'validate', 'compare', 'coverage'):
        command = sub.add_parser(name)
        if name == 'coverage':
            command.add_argument('revision', help='Git commit whose Base files must be fully present')
            continue
        command.add_argument('source', help='source path relative to the Julia Git repository')
        if name != 'validate':
            command.add_argument('revision', help='Git commit or revision')
    args = parser.parse_args()
    if args.command == 'coverage':
        target = revision(args.repo, args.revision)
        covered, problems, count = coverage(args.repo, args.root, target)
        sources = [s for s in git(args.repo, 'ls-tree', '-r', '-z', '--name-only', target, '--', 'base').decode().split('\0')
                   if s.endswith('.jl')]
        sources += sorted(s for s in covered if not s.startswith('base/'))
        missing_lines = 0
        for source in sources:
            total = len(lines(blob(args.repo, target, source)))
            missing = sorted(set(range(1, total + 1)) - covered.get(source, set()))
            if missing:
                missing_lines += len(missing)
                problems.append(f'{source}: {len(missing)} of {total} lines not in any source block (first {missing[0]})')
        for problem in problems:
            print(problem)
        print(f'SOURCE BLOCKS {count} FILES {len(sources)} MISSING LINES {missing_lines} PROBLEMS {len(problems)}')
        return int(bool(problems))
    source = source_path(args.source)
    model, proof = model_paths(args.root, source)
    if args.command == 'seed':
        sha = revision(args.repo, args.revision)
        original = blob(args.repo, sha, source)
        source_lines = lines(original)
        if not source_lines:
            raise ValueError('cannot represent an empty source file as an inclusive source range')
        rendered = b'-- UNTRANSLATED\n' + render(source, sha, 1, len(source_lines), source_lines)
        model.parent.mkdir(parents=True, exist_ok=True)
        with model.open('xb') as output:
            output.write(rendered)
        print(f'UNMODELLED UNTRANSLATED {model}: source comment only; no declarations or coverage')
        return 0
    entries = blocks(args.repo, model, source)
    if args.command == 'validate':
        print(f'VALID {model}: {len(entries)} source block(s)')
        return 0
    target = revision(args.repo, args.revision)
    new = blob(args.repo, target, source) if git(args.repo, 'ls-tree', '-z', target, '--', str(source)) else None
    changed = False
    for old, first, last, original, untranslated in entries:
        if untranslated:
            print(f'UNTRANSLATED {source}:{first}-{last} at {old}\n  model: {model}\n  proof: {proof}')
        if original != new:
            changed = True
            kind = ('source file missing' if new is None else
                    'snippet changed or shifted' if lines(original)[first - 1:last] != lines(new)[first - 1:last] else
                    'source file changed outside snippet')
            print(f'CHANGED {source}:{first}-{last} {old} -> {target}: {kind}\n  model: {model}\n  proof: {proof}')
    if not changed:
        print(f'UNCHANGED {source} at {target}')
    return int(changed)


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, UnicodeError) as error:
        print(f'error: {error}', file=sys.stderr)
        sys.exit(2)
