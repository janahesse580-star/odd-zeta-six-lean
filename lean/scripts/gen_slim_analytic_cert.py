#!/usr/bin/env python3
"""
Generate the slim 4-bin, 2-root-pair analytic certificate shards for OddZetaSix.

Every rational arithmetic step matches `OddZetaSix/SixAnalyticCertCore.lean`
bit-for-bit (exact Fraction arithmetic with directed rounding at d = 10^5 / 10^6,
n = 5 / 6 series terms). Outputs 4 balanced shards under
`OddZetaSix/AnalyticData/Shard{0,1,2,3}.lean` verified purely by `decide +kernel`.
"""
from fractions import Fraction
from collections import defaultdict
from pathlib import Path


def floor_q(q: Fraction) -> int:
    return q.numerator // q.denominator


def ceil_q(q: Fraction) -> int:
    return -((-q.numerator) // q.denominator)


def round_down(d: int, a: Fraction) -> Fraction:
    return Fraction(floor_q(a * d), d)


def round_up(d: int, a: Fraction) -> Fraction:
    return Fraction(ceil_q(a * d), d)


def atanh_err(x: Fraction, n: int) -> Fraction:
    return 2 * (x ** (2 * n + 1) / (1 - x * x))


def r_atanh_lo(x: Fraction, n: int, d: int) -> Fraction:
    return 2 * sum(round_down(d, x ** (2 * i + 1) / (2 * i + 1)) for i in range(n))


def r_atanh_hi(x: Fraction, n: int, d: int) -> Fraction:
    return 2 * sum(round_up(d, x ** (2 * i + 1) / (2 * i + 1)) for i in range(n)) + round_up(d, atanh_err(x, n))


def arg(y: Fraction) -> Fraction:
    return (y - 1) / (y + 1)


def log2_exp(q: Fraction) -> int:
    k = (q.numerator.bit_length() - 1) - (q.denominator.bit_length() - 1)
    m = q / (Fraction(2) ** k)
    if m < 1:
        return k - 1
    elif m > 2:
        return k + 1
    return k


def r_log_lo(q: Fraction, n: int, d: int) -> Fraction:
    k = log2_exp(q)
    m = q / (Fraction(2) ** k)
    assert 1 <= m <= 2, f"mantissa out of range for {q}: k={k}, m={m}"
    l2 = r_atanh_lo(arg(Fraction(2)), n, d) if k >= 0 else r_atanh_hi(arg(Fraction(2)), n, d)
    return r_atanh_lo(arg(m), n, d) + k * l2


def r_log_hi(q: Fraction, n: int, d: int) -> Fraction:
    k = log2_exp(q)
    m = q / (Fraction(2) ** k)
    assert 1 <= m <= 2, f"mantissa out of range for {q}: k={k}, m={m}"
    l2 = r_atanh_hi(arg(Fraction(2)), n, d) if k >= 0 else r_atanh_lo(arg(Fraction(2)), n, d)
    return r_atanh_hi(arg(m), n, d) + k * l2


PI_LO = Fraction(314159265358979323846, 10**20)
PI_HI = Fraction(314159265358979323847, 10**20)


def r_atan_small_lo(q: Fraction, n: int, d: int) -> Fraction:
    return sum(round_down(d, ((-1) ** i) * (q ** (2 * i + 1)) / (2 * i + 1)) for i in range(2 * n))


def r_atan_small_hi(q: Fraction, n: int, d: int) -> Fraction:
    return sum(round_up(d, ((-1) ** i) * (q ** (2 * i + 1)) / (2 * i + 1)) for i in range(2 * n + 1))


def r_atan_lo(q: Fraction, n: int, d: int) -> Fraction:
    if q <= Fraction(1, 2):
        return r_atan_small_lo(q, n, d)
    if q <= 1:
        return PI_LO / 4 - r_atan_small_hi((1 - q) / (1 + q), n, d)
    if q <= 2:
        return PI_LO / 4 + r_atan_small_lo((q - 1) / (q + 1), n, d)
    return PI_LO / 2 - r_atan_small_hi(1 / q, n, d)


def r_atan_hi(q: Fraction, n: int, d: int) -> Fraction:
    if q <= Fraction(1, 2):
        return r_atan_small_hi(q, n, d)
    if q <= 1:
        return PI_HI / 4 - r_atan_small_lo((1 - q) / (1 + q), n, d)
    if q <= 2:
        return PI_HI / 4 + r_atan_small_hi((q - 1) / (q + 1), n, d)
    return PI_HI / 2 - r_atan_small_lo(1 / q, n, d)


ZEROS = [40, 40, 40, 41, 43]
OFFSETS = [0, 0, 0, 0, 0, 2, 4, 5, 5, 6, 8, 9, 9, 11]
DELTA = Fraction(69, 50)
N_LOG, N_ATAN, D_RND = 5, 5, 100000
C_HI = Fraction(-290837, 1000000)

_x_terms = defaultdict(int)
_x_terms[Fraction(139, 50)] += 5
_x_terms[Fraction(1, 50)] += 5
for z in ZEROS:
    _x_terms[Fraction(z - 1, 50)] += 1
    _x_terms[Fraction(139 - z, 50)] -= 1
for d in OFFSETS:
    _x_terms[Fraction(44 + d, 50)] += 1
    _x_terms[Fraction(94 - d, 50)] -= 1
X_LIST = [(r, m) for r, m in sorted(_x_terms.items()) if m != 0]

BINS = [
    (Fraction(0), Fraction(3, 40), Fraction(4, 25), Fraction(21, 100)),
    (Fraction(3, 40), Fraction(3, 20), Fraction(4, 25), Fraction(1, 4)),
    (Fraction(3, 20), Fraction(9, 40), Fraction(4, 25), Fraction(7, 25)),
    (Fraction(9, 40), Fraction(3, 10), Fraction(4, 25), Fraction(3, 10)),
]

CAPS = [
    [Fraction(-878, 100), Fraction(-8925, 1000)],
    [Fraction(-8925, 1000), Fraction(-9035, 1000)],
    [Fraction(-9025, 1000), Fraction(-9115, 1000)],
    [Fraction(-9105, 1000), Fraction(-9165, 1000)],
]


def phi_hi_at(y: Fraction) -> Fraction:
    s = C_HI + 3 * PI_HI * y
    for d, m in X_LIST:
        q = d * d + y * y
        if m >= 0:
            s += m * ((d / 2) * r_log_hi(q, N_LOG, D_RND) - y * r_atan_lo(y / d, N_ATAN, D_RND))
        else:
            s += m * ((d / 2) * r_log_lo(q, N_LOG, D_RND) - y * r_atan_hi(y / d, N_ATAN, D_RND))
    return round_up(D_RND, s)


def d_hi_on(l: Fraction, r: Fraction) -> Fraction:
    s = 3 * PI_HI
    for d, m in X_LIST:
        if m >= 0:
            s -= m * r_atan_lo(l / d, N_ATAN, D_RND)
        else:
            s -= m * r_atan_hi(r / d, N_ATAN, D_RND)
    return round_up(D_RND, s)


def d_lo_on(l: Fraction, r: Fraction) -> Fraction:
    s = 3 * PI_LO
    for d, m in X_LIST:
        if m >= 0:
            s -= m * r_atan_hi(r / d, N_ATAN, D_RND)
        else:
            s -= m * r_atan_lo(l / d, N_ATAN, D_RND)
    return round_down(D_RND, s)


def pair_mod_upper(l: Fraction, r: Fraction, a: Fraction) -> Fraction:
    f1 = max(abs(l * l - a * a), abs(r * r - a * a)) ** 2
    f2 = (r + a) ** 2 + 4 * DELTA * DELTA
    f3 = max((l - a) ** 2, (r - a) ** 2) + 4 * DELTA * DELTA
    return round_up(D_RND, f1 * f2 * f3)


def check_cell(l: Fraction, r: Fraction):
    phi_l = phi_hi_at(l) + max(Fraction(0), d_hi_on(l, r)) * (r - l)
    phi_r = phi_hi_at(r) + max(Fraction(0), -d_lo_on(l, r)) * (r - l)
    use_left = (phi_l <= phi_r)
    phi_u = phi_l if use_left else phi_r
    uniq = [Fraction(4, 25), Fraction(21, 100), Fraction(1, 4), Fraction(7, 25), Fraction(3, 10)]
    lp = {a: r_log_hi(pair_mod_upper(l, r, a), N_LOG, D_RND) for a in uniq}
    for b, (t0, t1, a1, a2) in enumerate(BINS):
        lpair = lp[a1] + lp[a2]
        if phi_u + (t0 / 4) * lpair > CAPS[b][0]:
            return False, use_left
        if phi_u + (t1 / 4) * lpair > CAPS[b][1]:
            return False, use_left
    return True, use_left


def partition(l: Fraction, r: Fraction):
    ok, use_left = check_cell(l, r)
    if ok:
        return [(l, r, use_left)]
    m = (l + r) / 2
    return partition(l, m) + partition(m, r)


def fmt_q(q: Fraction) -> str:
    return f"{q.numerator}" if q.denominator == 1 else f"{q.numerator} / {q.denominator}"


def main():
    cells = partition(Fraction(0), Fraction(2))
    print(f"Total certified cells: {len(cells)}")
    assert cells[0][0] == 0 and cells[-1][1] == 2
    for i in range(len(cells) - 1):
        assert cells[i][1] == cells[i + 1][0]

    # Split into 4 balanced shards
    n_shards = 4
    out_dir = Path(__file__).resolve().parent.parent / "OddZetaSix" / "AnalyticData"
    out_dir.mkdir(parents=True, exist_ok=True)
    chunk_size = (len(cells) + n_shards - 1) // n_shards
    boundaries = []
    for s in range(n_shards):
        chunk = cells[s * chunk_size : (s + 1) * chunk_size]
        assert len(chunk) > 0
        start, stop = chunk[0][0], chunk[-1][1]
        boundaries.append((start, stop, len(chunk)))
        lines = [
            "import OddZetaSix.SixAnalyticCertCore",
            "",
            f"/-! Auto-generated analytic certificate shard {s}: [{start}, {stop}] ({len(chunk)} cells). -/",
            "",
            "set_option autoImplicit false",
            "set_option Elab.async false",
            "",
            "namespace OddZetaSix.AnalyticData",
            "",
            f"def shard{s}Cells : List AnalyticCell := [",
        ]
        for idx, (l, r, ul) in enumerate(chunk):
            comma = "," if idx + 1 < len(chunk) else ""
            bstr = "true" if ul else "false"
            lines.append(f"  ⟨{fmt_q(l)}, {fmt_q(r)}, {bstr}⟩{comma}")
        lines += [
            "]",
            "",
            f"theorem shard{s}_ok : checkCellChain ({fmt_q(start)}) ({fmt_q(stop)}) shard{s}Cells = true := by",
            "  decide +kernel",
            "",
            "end OddZetaSix.AnalyticData",
            "",
        ]
        shard_path = out_dir / f"Shard{s}.lean"
        shard_path.write_text("\n".join(lines), encoding="utf-8")
        print(f"Wrote {shard_path.name}: [{start}, {stop}] ({len(chunk)} cells)")

    print("Boundaries:", boundaries)


if __name__ == "__main__":
    main()
