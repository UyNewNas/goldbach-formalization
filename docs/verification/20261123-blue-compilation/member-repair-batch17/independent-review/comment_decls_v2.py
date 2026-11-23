"""Tactic-proof assignment discovery for static source review, not Lean parsing."""
import re
from comment_decls import mask_comments_and_strings


def proof_assignment(text, start, end):
    masked = mask_comments_and_strings(text)
    stack = []
    pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
    i = start
    while i < end:
        ch = masked[i]
        if ch in '([{⟨':
            stack.append(ch)
        elif ch in pairs:
            assert stack and stack.pop() == pairs[ch], (i, ch)
        elif not stack and masked.startswith(':=', i):
            # Header-level lets may contain :=. Only the actual tactic proof
            # assignment is accepted, never an arbitrary first := token.
            if re.match(r':=\s*by\b', masked[i:end]):
                return i
        i += 1
    raise ValueError('no top-level tactic proof assignment in reviewed declaration')
