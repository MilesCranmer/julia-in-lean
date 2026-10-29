"""Content bindings for full registry exports and independently produced reviews.

The pinned Julia source is staged under coverage/src/ (not tracked by git):
mkdir -p coverage/src && git -C <julia-source-root> archive <SOURCE_COMMIT> base | tar -x -C coverage/src
"""
import csv
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def binding_path(path):
    return path.with_name(path.name + '.evidence.json')


def metadata_path(path):
    return path.with_name(path.name + '.metadata.jsonl')


def write_binding(path, data):
    target = binding_path(path)
    temporary = target.with_name(target.name + '.tmp')
    temporary.write_text(json.dumps(data, sort_keys=True) + '\n')
    temporary.replace(target)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f'duplicate JSON key {key}')
        result[key] = value
    return result


def load_metadata(registry):
    rows = {}
    for number, line in enumerate(registry.read_text().splitlines(), 1):
        fields = line.split('\t')
        if len(fields) != 6 or not fields[0] or fields[0] in rows:
            raise ValueError(f'{registry}:{number}: malformed or duplicate registry entry')
        rows[fields[0]] = fields
    result = {}
    keys = {'id', 'status', 'julia_file', 'julia_functions', 'statement', 'source',
            'property', 'theorem', 'property_module', 'theorem_module'}
    for number, line in enumerate(metadata_path(registry).read_text().splitlines(), 1):
        obj = json.loads(line, object_pairs_hook=unique_object)
        if not isinstance(obj, dict) or set(obj) != keys:
            raise ValueError(f'invalid metadata row {number}')
        ident = obj['id']
        if not isinstance(ident, str) or ident in result or ident not in rows:
            raise ValueError(f'metadata identity mismatch: {ident!r}')
        row = rows[ident]
        if (not isinstance(obj['statement'], str) or not isinstance(obj['status'], str) or obj['status'] not in {'todo', 'proven', 'refuted'} or
                (obj['status'], obj['julia_file'], obj['statement'].replace('\t', ' ').replace('\n', ' ')) != (row[1], row[3], row[5])):
            raise ValueError(f'metadata identity mismatch: {ident}')
        if (not isinstance(obj['julia_functions'], list) or
                any(not isinstance(x, str) for x in obj['julia_functions']) or
                not isinstance(obj['source'], str) or
                any(not isinstance(obj[k], str) or not obj[k] for k in ('property', 'property_module'))):
            raise ValueError(f'invalid metadata payload: {ident}')
        if obj['status'] == 'todo':
            if obj['theorem'] is not None or obj['theorem_module'] is not None:
                raise ValueError(f'invalid todo metadata: {ident}')
        elif any(not isinstance(obj[k], str) or not obj[k] for k in ('theorem', 'theorem_module')):
            raise ValueError(f'invalid theorem metadata: {ident}')
        result[ident] = obj
    if set(result) != set(rows):
        raise ValueError('metadata registry ids differ')
    return result


def module_closure(root, modules):
    paths = set()
    pending = list(modules)
    seen = set()
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*', module):
            raise ValueError(f'invalid module {module!r}')
        path = root / (module.replace('.', '/') + '.lean')
        if not path.is_file():
            if module == 'Lean' or module.startswith(('Lean.', 'Std.')) or module == 'Std':
                continue
            raise ValueError(f'missing Lean module {module}')
        paths.add(path)
        text = path.read_text()
        # Preserve newlines while removing nested Lean comments.
        clean = []
        depth = 0
        quoted = False
        escaped = False
        i = 0
        while i < len(text):
            pair = text[i:i + 2]
            if not depth and quoted:
                char = text[i]
                clean.append(char)
                if char == '"' and not escaped:
                    quoted = False
                escaped = char == '\\' and not escaped
                i += 1
            elif not depth and text[i] == '"':
                quoted = True
                escaped = False
                clean.append(text[i])
                i += 1
            elif pair == '/-':
                depth += 1
                clean.extend('  ')
                i += 2
            elif depth and pair == '-/':
                depth -= 1
                clean.extend('  ')
                i += 2
            elif not depth and pair == '--':
                end = text.find('\n', i)
                end = len(text) if end < 0 else end
                clean.extend(' ' * (end - i))
                i = end
            else:
                clean.append('\n' if text[i] == '\n' else (' ' if depth else text[i]))
                i += 1
        if depth:
            raise ValueError(f'unterminated comment in {path}')
        text = ''.join(clean)
        for match in re.finditer(r'^\s*(?:public\s+)?import\s+([^\n]+)', text, re.M):
            pending.extend(match.group(1).split())
    return paths


def hash_paths(root, paths, payload=None):
    h = hashlib.sha256()
    for path in sorted(paths):
        name = path.relative_to(root).as_posix().encode()
        h.update(len(name).to_bytes(8, 'big'))
        h.update(name)
        h.update(bytes.fromhex(digest(path)))
    if payload is not None:
        h.update(json.dumps(payload, sort_keys=True, separators=(',', ':')).encode())
    return h.hexdigest()


def snapshot(root=ROOT):
    paths = {root / name for name in ('lean-toolchain', 'lakefile.toml', 'Report.lean',
             'Audit.lean', 'scripts/audit.sh', 'coverage/SOURCE_COMMIT',
             'scripts/coverage_metadata.lean')}
    paths |= module_closure(root, ['Report', 'Audit', 'JuliaLean.Registry.Metadata'])
    base = root / 'coverage/src/base'
    if not base.is_dir():
        raise ValueError('missing staged Base source')
    paths.update(base.rglob('*.jl'))
    paths.update((root / 'repro').rglob('*.jl'))
    return hash_paths(root, paths)


def review_snapshot(manifest, registry, root=ROOT):
    metadata = load_metadata(registry)
    with manifest.open(newline='') as fh:
        reader = csv.DictReader(fh, delimiter='\t')
        fields = ['file', 'line', 'endline', 'name', 'signature', 'status', 'entry', 'note']
        if reader.fieldnames != fields:
            raise ValueError('invalid manifest schema')
        rows = list(reader)
    ids, sources = set(), set()
    for row in rows:
        if None in row or any(v is None for v in row.values()):
            raise ValueError('malformed manifest row')
        file = row['file']
        if not file.startswith('base/') or not file.endswith('.jl') or any(p in ('', '.', '..') for p in file.split('/')) or '\\' in file:
            raise ValueError(f'invalid source path {file!r}')
        sources.add(root / 'coverage/src' / file)
        ids.update(row['entry'].split(',') if row['entry'] else [])
    if not ids <= metadata.keys():
        raise ValueError('manifest references missing registry id')
    selected = {ident: metadata[ident] for ident in sorted(ids)}
    modules = {entry[k] for entry in selected.values() for k in ('property_module', 'theorem_module') if entry[k]}
    paths = module_closure(root, modules) | sources
    paths.add(root / 'coverage/REVIEW_PROMPT.md')
    paths.add(root / 'coverage/SOURCE_COMMIT')
    for ident, entry in selected.items():
        if entry['status'] == 'refuted':
            paths.add(root / 'repro' / (ident + '.jl'))
    registry_rows = {fields[0]: fields for fields in
                     (line.split('\t') for line in registry.read_text().splitlines())}
    payload = {ident: {'metadata': entry, 'registry': registry_rows[ident]}
               for ident, entry in selected.items()}
    return {'version': 2, 'snapshot': hash_paths(root, paths, payload), 'manifest': digest(manifest)}


def registry_binding(registry, root=ROOT):
    load_metadata(registry)
    return {'version': 2, 'snapshot': snapshot(root), 'registry': digest(registry),
            'metadata': digest(metadata_path(registry))}


def review_state(path):
    if not path.exists():
        return None
    info = path.stat()
    return [info.st_ino, info.st_mtime_ns, info.st_ctime_ns, digest(path)]


def main():
    action, *args = sys.argv[1:]
    if action == 'snapshot' and len(args) == 1:
        Path(args[0]).write_text(snapshot() + '\n')
    elif action == 'bind-registry' and len(args) == 2:
        before, registry = map(Path, args)
        binding = registry_binding(registry)
        if before.read_text().strip() != binding['snapshot']:
            raise ValueError('inputs changed during registry verification')
        write_binding(registry, binding)
    elif action == 'review-snapshot' and len(args) == 3:
        target, manifest, review = map(Path, args)
        saved = review_snapshot(manifest, ROOT / 'registry.tsv')
        saved.update(review_path=str(review.resolve()), review_state=review_state(review))
        target.write_text(json.dumps(saved, sort_keys=True) + '\n')
    elif action == 'bind-review' and len(args) == 3:
        before, manifest, review = map(Path, args)
        saved = json.loads(before.read_text())
        if saved.pop('review_path') != str(review.resolve()):
            raise ValueError('review path differs from snapshot')
        old_review = saved.pop('review_state')
        if saved != review_snapshot(manifest, ROOT / 'registry.tsv'):
            raise ValueError('inputs changed during review')
        if review_state(review) == old_review:
            raise ValueError('review was not written after the snapshot')
        write_binding(review, {**saved, 'review': digest(review)})
    else:
        raise ValueError('usage: snapshot FILE | bind-registry SNAPSHOT REGISTRY | review-snapshot FILE MANIFEST REVIEW | bind-review SNAPSHOT MANIFEST REVIEW')


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
