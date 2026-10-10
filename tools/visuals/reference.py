"""Independent reference calculations for the illustrations (used by tools/validate_site.py).

Written from the paper's descriptions, not from the browser code or the Lean code:
  * two-frame restoration (Section 5.3 and Appendix C): delta bit k is the OR over heaps of the bit-k XORs;
    the reply is the first heap x with x XOR delta < x, else the first nonzero heap minus one, else no move;
    the output fields are a validity bit, an index of floor(log2 N) + 1 bits and B value bits, big-endian;
  * structured rollouts (Proposition 5.9 and Appendix C): pi_j subtracts 2^j from the first heap of size at
    least 2^j, otherwise 1 from the first nonzero heap; the outcome is the parity of the number of moves, which
    must equal sigma_0 for j = 0 and sigma_j XOR sigma_0 otherwise; the number of moves of pi_j is
    sum over heaps of (h div 2^j) + (h mod 2^j); the all-head schedule uses M + 2B + 2 evaluations;
  * recurrence (Section 5.5): one decision reports the nim-sum and the difference from the previous summary,
    and plays the first cancelling heap, else the first nonzero heap minus one; replay uses 2N + 2 updates
    per decision, board storage N + 1.
"""
from functools import reduce


def nim(P):
    return reduce(lambda a, b: a ^ b, P, 0)


def index_width(N):
    return max(N, 1).bit_length()          # floor(log2 N) + 1, and 1 for N = 0


def bits_be(x, B):
    return [bool((x >> (B - 1 - p)) & 1) for p in range(B)]


def reply(target, P):
    for i, x in enumerate(P):
        if x ^ target < x:
            return (i, x ^ target), "cancel"
    for i, x in enumerate(P):
        if x > 0:
            return (i, x - 1), "fallback"
    return None, "terminal"


def restore(B, Q, Qp):
    delta = 0
    for k in range(B):
        if any(((a >> k) & 1) != ((b >> k) & 1) for a, b in zip(Q, Qp)):
            delta |= 1 << k
    move, branch = reply(delta, Qp)
    r = index_width(len(Qp))
    wires = [move is not None] + (bits_be(move[0], r) if move else [False] * r) + (bits_be(move[1], B) if move else [False] * B)
    return {"delta": delta, "move": list(move) if move else None, "branch": branch, "wires": wires,
            "candidates": sum(1 for x in Qp if x ^ delta < x)}


def policy_step(j, P):
    u = 2 ** j
    for i, x in enumerate(P):
        if x >= u:
            return i, x - u
    for i, x in enumerate(P):
        if x > 0:
            return i, x - 1
    return None


def rollout_moves(j, P):
    P, n = list(P), 0
    while True:
        m = policy_step(j, P)
        if m is None:
            return n
        P[m[0]] = m[1]
        n += 1


def rollouts(B, P, early=False):
    s = nim(P)
    moves = [rollout_moves(j, P) for j in range(B)]
    formula = [sum(h // 2 ** j + h % 2 ** j for h in P) for j in range(B)]
    outs = [m % 2 == 1 for m in moves]
    channel = [bool(s & 1)] + [bool((s >> j) & 1) != bool(s & 1) for j in range(1, B)]
    res = {"moves": moves, "moves_formula_ok": moves == formula, "outs": outs, "channel_ok": outs == channel}
    if early:
        heads = next((j + 1 for j, o in enumerate(outs) if o), B)
        res["heads"] = heads
        res["evaluations"] = 1 + sum(moves[j] + 2 for j in range(heads))
        res["decision"] = any(outs)
    else:
        # recover sigma from the outcomes as the readout does: sigma_0 = o_0, sigma_j = o_j XOR o_0
        sigma = sum(1 << j for j in range(B) if (outs[j] if j == 0 else outs[j] != outs[0]))
        res["sigma"] = sigma
        res["sigma_ok"] = sigma == s
        res["evaluations"] = sum(moves) + 2 * B + 2
        move, branch = reply(sigma, P)
        res["readout"] = list(move) if move else None
        res["branch"] = branch
    return res


def decisions(boards, protocol="replay"):
    """Outputs and update counts for consecutive decisions on the given boards (one game)."""
    out, prev = [], None
    for P in boards:
        move, _ = reply(nim(P), P)
        o = {"summary": nim(P), "move": list(move) if move else None,
             "updates": 2 * len(P) + 2 if protocol == "replay" else len(P) + 1}
        if protocol == "replay":
            o["diff"] = None if prev is None else nim(prev) ^ nim(P)
        out.append(o)
        prev = P
    return out
