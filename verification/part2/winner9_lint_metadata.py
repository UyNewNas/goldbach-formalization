"""Recover only the historical lint filename of a fixed public P2.10 module.

This module performs no I/O writes and never invokes Lean. A source/reference
gate precedes the byte operation; the result must equal the complete historical
SHA256 before it is returned. The caller keeps the original Lake object and
all of its trace/hash sidecars unchanged.

The narrow parser follows Lean commit 62eed1db4d67327ec8120be05f1a1b0847d74561:
src/library/module.cpp, src/runtime/compact.cpp, src/include/lean/lean.h,
src/util/name.h, and src/Lean/Linter/PersistentLintLog.lean. Only v2 x64 GMP
headers and ctor/Array/String objects are supported. This is not an olean
validator or a replacement for the original compilation/replay/audit gates.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import struct


COMMIT = "62eed1db4d67327ec8120be05f1a1b0847d74561"
REFERENCE_SHA = "ee3d1b8d4dd962ba4195b90299062ab972de82422cb24114822a1a5442e77689"
BASELINE = "8657cfffef159185f73c6a04ae4d31c846c0d0a9"
HEADER = b"olean\x02\x01" + b"4.33.0-rc1".ljust(33, b"\0") + COMMIT.encode()
BASELINE_ROOT = Path("/workspace/goldbach-p2")


def need(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def aligned(size):
    return (size + 7) // 8 * 8


class View:
    def __init__(self, data):
        need(len(data) >= 104 and len(data) % 8 == 0 and data[:80] == HEADER,
             "Unsupported compiler header or object size")
        self.data = data
        self.base = self.word(80)
        need(self.base % 65536 == 0, "Unaligned logical base")
        self.order, self.slots = [], [88]
        position = 96
        while position < len(data):
            rc, size, count, tag = struct.unpack_from("<iHBB", data, position)
            need(rc == 0, "Unexpected heap object")
            if tag <= 243:
                need(size >= 8 + 8 * count, "Truncated constructor")
                object_size = size
                self.slots.extend(range(position + 8, position + 8 + 8 * count, 8))
            elif tag == 246:
                need(position + 24 <= len(data), "Truncated Array header")
                length, capacity = struct.unpack_from("<QQ", data, position + 8)
                need(size == 1 and length == capacity, "Noncompact Array")
                object_size = 24 + 8 * length
                need(position + object_size <= len(data), "Truncated Array")
                self.slots.extend(range(position + 24, position + object_size, 8))
            elif tag == 249:
                need(position + 32 <= len(data), "Truncated String header")
                length, capacity, _ = struct.unpack_from("<QQQ", data, position + 8)
                need(size == 1 and length == capacity and length > 0, "Noncompact String")
                object_size = 32 + length
                need(position + object_size <= len(data), "Truncated String")
                need(data[position + object_size - 1] == 0, "Unterminated String")
            else:
                raise ValueError(f"Unsupported object tag {tag}; metadata recovery refused")
            need(position + object_size <= len(data), "Object extends past file")
            self.order.append((position, object_size, count, tag))
            position += aligned(object_size)
        need(position == len(data), "Invalid final object boundary")
        self.objects = {item[0]: item for item in self.order}
        self.index = {item[0]: i for i, item in enumerate(self.order)}
        for slot in self.slots:
            value = self.word(slot)
            if value & 1:
                need(slot != 88, "Scalar ModuleData root")
            else:
                need(value - self.base in self.objects, "Pointer does not target an object start")
        self.name_cache = {}

    def word(self, offset):
        return struct.unpack_from("<Q", self.data, offset)[0]

    def field(self, offset, index):
        return self.word(offset + 8 + 8 * index)

    def require_ctor(self, offset, size, count, tag=0):
        need(self.objects.get(offset) == (offset, size, count, tag), "Unexpected metadata object shape")

    def string(self, pointer):
        offset = pointer - self.base
        need(offset in self.objects and self.objects[offset][3] == 249, "Expected String")
        return self.data[offset + 32:offset + 32 + self.word(offset + 8) - 1].decode("utf-8")

    def name(self, pointer):
        if pointer == 1:
            return ()
        if pointer in self.name_cache:
            return self.name_cache[pointer]
        offset = pointer - self.base
        need(offset in self.objects, "Name outside object graph")
        _, size, count, tag = self.objects[offset]
        need(size == 32 and count == 2 and tag in (1, 2), "Unexpected Name shape")
        value = self.field(offset, 1)
        if tag == 1:
            component = self.string(value)
        else:
            need(value & 1, "Unsupported numeral Name")
            component = value // 2
        result = self.name(self.field(offset, 0)) + (component,)
        self.name_cache[pointer] = result
        return result

    def array(self, pointer):
        offset = pointer - self.base
        need(offset in self.objects and self.objects[offset][3] == 246, "Expected Array")
        return [self.word(offset + 24 + 8 * i) for i in range(self.word(offset + 8))]

    def children(self, offset):
        _, _, count, tag = self.objects[offset]
        if tag <= 243:
            values = [self.field(offset, i) for i in range(count)]
        elif tag == 246:
            values = self.array(self.base + offset)
        else:
            need(tag == 249, "Unsupported object kind")
            values = []
        return [value - self.base for value in values if value & 1 == 0]

    def reachable(self, offset):
        todo, seen = [offset], set()
        while todo:
            current = todo.pop()
            if current not in seen:
                seen.add(current)
                todo.extend(self.children(current))
        return seen

    def lint_filename(self):
        root = self.word(88) - self.base
        self.require_ctor(root, 56, 5)
        need(self.data[root + 48] == 0, "Expected legacy ModuleData")
        lint_arrays, other_arrays, extension_keys = [], [], []
        for pointer in self.array(self.field(root, 4)):
            pair = pointer - self.base
            self.require_ctor(pair, 24, 2)
            key_pointer = self.field(pair, 0)
            extension_keys.append(key_pointer)
            values = self.field(pair, 1)
            if self.name(key_pointer) == ("Lean", "Linter", "lintLogExt"):
                lint_arrays.append(values)
            else:
                other_arrays.append(values)
        need(len(lint_arrays) == 1, "Exactly one lintLogExt is required for metadata recovery")
        lints = self.array(lint_arrays[0])
        need(bool(lints), "Empty lintLogExt")
        file_pointers = set()
        for pointer in lints:
            entry = pointer - self.base
            self.require_ctor(entry, 40, 4)
            message = self.field(entry, 1) - self.base
            self.require_ctor(message, 24, 2)
            base_message = self.field(message, 0) - self.base
            self.require_ctor(base_message, 56, 5)
            file_pointers.update((self.field(entry, 3), self.field(base_message, 0)))
        need(len(file_pointers) == 1, "Lint filenames do not share one String")
        pointer = next(iter(file_pointers))
        filename, offset = self.string(pointer), pointer - self.base
        for i in range(4):
            need(offset not in self.reachable(self.field(root, i) - self.base),
                 "Filename reaches constants or another non-extension ModuleData field")
        for value in other_arrays + extension_keys:
            need(offset not in self.reachable(value - self.base), "Filename escapes lintLogExt values")
        return offset, filename, [self.index[p - self.base] for p in lints]

    def bytes_except_filename(self, target):
        result = bytearray(self.data)
        for slot in self.slots:
            value = self.word(slot)
            if value & 1 == 0:
                struct.pack_into("<Q", result, slot, self.index[value - self.base])
        end = target + aligned(self.objects[target][1])
        return bytes(result[:target] + result[end:])


def rewrite_filename(original, expected_filename, filename):
    """Pure internal byte operation; canonicalize() supplies all authority gates."""
    target, actual_filename, lint_order = original.lint_filename()
    need(actual_filename == expected_filename, "Lint filename differs from the actual logical source path")
    for offset, _, _, tag in original.order:
        if tag == 249 and offset != target:
            need(original.string(original.base + offset) != filename, "Filename would change String sharing")
    raw = filename.encode("utf-8")
    need(raw.isascii() and b"\0" not in raw, "Expected an ASCII path without NUL")
    size = len(raw) + 1
    replacement = original.data[target:target + 8] + struct.pack("<QQQ", size, size, len(filename)) + raw + b"\0"
    replacement += b"\0" * (aligned(len(replacement)) - len(replacement))
    old_end = target + aligned(original.objects[target][1])
    delta = len(replacement) - (old_end - target)
    output = bytearray(original.data[:target] + replacement + original.data[old_end:])
    for slot in original.slots:
        need(not target <= slot < old_end, "String unexpectedly contains pointer slots")
        value = original.word(slot)
        if value & 1:
            continue
        old_target = value - original.base
        new_slot = slot + (delta if slot >= old_end else 0)
        new_target = old_target + (delta if old_target >= old_end else 0)
        struct.pack_into("<Q", output, new_slot, original.base + new_target)
    data = bytes(output)
    updated = View(data)
    expected_layout = [(offset + (delta if offset >= old_end else 0),
                        32 + size if offset == target else object_size, count, tag)
                       for offset, object_size, count, tag in original.order]
    need(updated.order == expected_layout, "Object order or non-String layout changed")
    need(updated.data[:88] == original.data[:88], "Compiler header or logical base changed")
    updated_target, updated_filename, updated_lints = updated.lint_filename()
    need(updated_target == target and updated_filename == filename and updated_lints == lint_order,
         "Lint structure, entry order, or sharing changed")
    need(updated.bytes_except_filename(target) == original.bytes_except_filename(target),
         "Non-filename object bytes or pointer targets changed")
    return data, {"from_filename": expected_filename, "to_filename": filename,
                  "lint_entries": len(lint_order), "filename_object_offset": target,
                  "size_delta": delta, "all_other_object_bytes_and_pointer_targets_identical": True,
                  "lint_entry_order_and_sharing_identical": True}


def canonicalize(data, *, module, root, reference_bytes):
    """Return historical bytes only after exact public source/object SHA gates."""
    need(digest(reference_bytes) == REFERENCE_SHA, "Unexpected public reference bytes")
    reference = json.loads(reference_bytes)
    need(len(reference) == 93 and module in reference, "Module is outside the fixed public 93")
    record = reference[module]
    need(record.get("baseline_commit") == BASELINE, "Only historical baseline modules use this helper")
    relative_source = module.replace(".", "/") + ".lean"
    need(record["source"] == relative_source and record["module"] == module, "Source/module mismatch")
    root = Path(root).resolve()
    source = root / relative_source
    need(source.resolve().is_relative_to(root) and source.is_file()
         and digest(source.read_bytes()) == record["source_sha256"], "Source differs from public record")
    input_sha = digest(data)
    expected_sha = record["object_sha256"]
    report = {"module": module, "source_sha256": record["source_sha256"],
              "reference_sha256": REFERENCE_SHA, "raw_sha256": input_sha,
              "historical_sha256": expected_sha, "raw_bytes": len(data),
              "new_compilation_credit": 0, "new_replay_credit": 0}
    if input_sha == expected_sha:
        return data, {**report, "method": "already-identical", "historical_bytes": len(data)}
    original = View(data)
    expected_filename = str(source)
    historical_filename = str(BASELINE_ROOT / relative_source)
    identity, _ = rewrite_filename(original, expected_filename, expected_filename)
    need(identity == data, "Original-filename identity reconstruction differs")
    candidate, details = rewrite_filename(original, expected_filename, historical_filename)
    actual_sha = digest(candidate)
    need(actual_sha == expected_sha,
         f"{module}: lint-only candidate SHA {actual_sha} differs from historical {expected_sha}")
    return candidate, {**report, **details, "method": "lint-filename-only",
                       "identity_differing_bytes": 0, "historical_bytes": len(candidate)}
