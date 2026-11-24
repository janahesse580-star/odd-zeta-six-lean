"""Generate slim, zero-Mathlib Lean 4 arithmetic certificate shards for OddZetaSix.

Produces:
  1. OddZetaSix/PeriodicData/Shard0.lean .. Shard3.lean
     (1,808 crossing-free 12-line periodic pieces on [0, 1], verified pure-rational
      12-period + tail bound C0 <= 552/1000)
  2. OddZetaSix/HighData/Shard0.lean .. Shard5.lean
     (506 merged flat 12-line folded high tiles on [7/2, 55] using only joint0..joint6,
      verified exact rational integral C1 <= 7206/1000)

Uses pure integer arithmetic (fixed denominator D = 10^8) matching
OddZetaSix/SixFoldedCertCore.lean bit-for-bit, so every shard compiles rapidly
under `decide +kernel` with zero `native_decide` and zero `sorry`.
"""

from __future__ import annotations

import json
from fractions import Fraction as Q
from pathlib import Path
from typing import List, Tuple

CERT_DEN = 100_000_000  # 10^8, matching OddZetaSix.CertCore.certDen

RADII = [14, 16, 17, 19, 20, 21, 23, 25, 27, 29, 30, 70]
POLE_MULT = [1, 2, 1, 1, 2, 1, 1, 5, 0, 0, 0, 0]
SIGNED_WT = [1, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, -5]
ZSET = (40, 41, 43)


def ceil_div(num: int, den: int) -> int:
    assert den > 0
    return (num + den - 1) // den


def aff_int_ceil(a0: int, a1: int, ln: int, ld: int, rn: int, rd: int, D: int) -> int:
    dx = rn * ld - ln * rd
    sum2 = 2 * a0 * ld * rd + a1 * (ln * rd + rn * ld)
    num = dx * sum2
    den = 2 * (ld * rd) * (ld * rd)
    return 0 if num <= 0 else ceil_div(num * D, den)


def periodic_12_ceil(a0: int, a1: int, ln: int, ld: int, rn: int, rd: int) -> int:
    acc = 0
    for k in range(12):
        clip = (k == 0 and 7 * ln < 2 * ld)
        uln = 2 if clip else ln
        uld = 7 if clip else ld
        if uln * rd < rn * uld:
            xn = k * uld + uln
            xd = uld
            dx = rn * uld - uln * rd
            sum2 = 2 * a0 * uld * rd + a1 * (uln * rd + rn * uld)
            numI = dx * sum2
            denI = 2 * (uld * rd) * (uld * rd)
            wNum = 6 * xd * xd * xn + xd * xd * xd
            wDen = 6 * xn * xn * xn
            if numI > 0:
                acc += ceil_div(numI * wNum * CERT_DEN, denI * wDen)
    return acc


def refined_slots(m: int, base_val: int, denom_aliases: int, num_aliases: int,
                  right: int, left: int) -> List[int]:
    raw = []
    for r in range(m):
        best = 0
        for l in range(m):
            if r <= m - 1 - l:
                d = m - 1 - l - r
                d_eff = min(d, num_aliases) if denom_aliases == 0 else d
                ind = (1 if right >= 1 else 0) if (l % 2 == 0) else (1 if left < right else 0)
                v = r - base_val + d_eff + (l + 5) * ind
                if v > best:
                    best = v
        raw.append(best)
    # suffix maxima
    res = [0] * m
    cur = 0
    for r in range(m - 1, -1, -1):
        if raw[r] > cur:
            cur = raw[r]
        res[r] = cur
    return res


def hist_joint_caps(hist: List[int], q: int) -> List[int]:
    caps = [0] * 19
    r = 0
    for v in range(18, 0, -1):
        c = hist[v]
        for idx in range(r, r + c):
            pen = 0 if idx <= q else 2 * (idx - q)
            inc = v - pen
            if inc > 0:
                for j in range(1, inc + 1):
                    caps[j] += 1
        r += c
    return caps


def cap_int_ceil(u0: int, u1: int, ln: int, ld: int, rn: int, rd: int, D: int) -> int:
    va = u0 * ld + u1 * ln
    vb = u0 * rd + u1 * rn
    capL = 30 * ld
    capR = 30 * rd
    dx = rn * ld - ln * rd
    if va <= capL and vb <= capR:
        num = dx * (va * rd + vb * ld)
        den = 4 * (ld * rd) * (ld * rd)
        return 0 if num <= 0 else ceil_div(num * D, den)
    elif capL <= va and capR <= vb:
        num = 15 * dx
        den = ld * rd
        return 0 if num <= 0 else ceil_div(num * D, den)
    elif va < capL and capR < vb:
        s = u1
        assert s > 0
        diff = capL - va
        num = 60 * ld * s * dx - rd * diff * diff
        den = 4 * ld * ld * rd * s
        return 0 if num <= 0 else ceil_div(num * D, den)
    else:
        s = -u1
        assert s > 0
        diff = capR - vb
        num = 60 * rd * s * dx - ld * diff * diff
        den = 4 * ld * rd * rd * s
        return 0 if num <= 0 else ceil_div(num * D, den)


def build_periodic_pieces() -> List[dict]:
    walls = {Q(0), Q(1)}
    for r in RADII:
        for m in range(1, 2 * r):
            walls.add(Q(m, 2 * r))
    for z in ZSET:
        for m in range(1, z):
            walls.add(Q(m, z))
    for i, r in enumerate(RADII):
        for s in RADII[i + 1:]:
            for k in (r + s, s - r):
                for m in range(1, k):
                    walls.add(Q(m, k))
    walls_sorted = sorted(walls)

    pieces = []
    for l, r in zip(walls_sorted, walls_sorted[1:]):
        ln, ld = l.numerator, l.denominator
        rn, rd = r.numerator, r.denominator
        t = (l + r) / 2
        q2s = []
        for rad in RADII:
            q2 = (2 * rad * (ln * rd + rn * ld)) // (2 * ld * rd)
            assert q2 * ld <= 2 * rad * ln and 2 * rad * rn <= (q2 + 1) * rd
            q2s.append(q2)
        z40 = (40 * (ln * rd + rn * ld)) // (2 * ld * rd)
        z41 = (41 * (ln * rd + rn * ld)) // (2 * ld * rd)
        z43 = (43 * (ln * rd + rn * ld)) // (2 * ld * rd)
        for z, qz in ((40, z40), (41, z41), (43, z43)):
            assert qz * ld <= z * ln and z * rn <= (qz + 1) * rd
        vfact = sum(POLE_MULT[i] * q2s[i] for i in range(12)) - 2 * (3 * z40 + z41 + z43)

        lines = []
        for i, rad in enumerate(RADII):
            q = q2s[i] // 2
            if q2s[i] % 2 == 0:
                ab = (-2 * q, 2 * rad)
            else:
                ab = (2 * (q + 1), -2 * rad)
            lines.append((ab[0] + ab[1] * t, i, ab))
        lines.sort(key=lambda x: (x[0], x[1]))
        perm = [x[1] for x in lines]
        pts = [(0, 0)] + [x[2] for x in lines] + [(1, 0)]
        for u, v in zip(pts, pts[1:]):
            assert u[0] * ld + u[1] * ln <= v[0] * ld + v[1] * ln
            assert u[0] * rd + u[1] * rn <= v[0] * rd + v[1] * rn

        pos = [0] * 12
        for rank_idx, rad_idx in enumerate(perm):
            pos[rad_idx] = rank_idx

        a0 = 0
        a1 = 0
        for g in range(13):
            u, v = pts[g], pts[g + 1]
            val = 4 - vfact
            for i in range(12):
                q = q2s[i] // 2
                if q2s[i] % 2 == 0:
                    delta = 2 * q + (1 if g <= pos[i] else 0)
                else:
                    delta = 2 * q + (1 if g <= pos[i] else 2)
                val += SIGNED_WT[i] * delta
            B = max(0, val)
            a0 += B * (v[0] - u[0])
            a1 += B * (v[1] - u[1])

        assert a0 * ld + a1 * ln >= 0 and a0 * rd + a1 * rn >= 0
        fbar_num = aff_int_ceil(a0, a1, ln, ld, rn, rd, CERT_DEN)
        c0_num = periodic_12_ceil(a0, a1, ln, ld, rn, rd)
        pieces.append(dict(
            ln=ln, ld=ld, rn=rn, rd=rd,
            perm=perm, a0=a0, a1=a1,
            fbarNum=fbar_num, c0Num=c0_num,
        ))
    return pieces


def build_high_tiles(cert_path: Path) -> List[dict]:
    d = json.loads(cert_path.read_text(encoding="utf-8"))
    cut = Q(7, 100)
    hi_tiles = [t for t in d["high"] if Q(t[1]) > cut]

    def tile_key(l: Q, r: Q):
        mid = (l + r) / 2
        K30 = int(30 / mid)
        q2s = tuple(int((2 * rad) / mid) for rad in RADII)
        qzs = tuple(int(z / mid) for z in ZSET)
        flines = []
        for idx, rad in enumerate(RADII):
            q = q2s[idx] // 2
            side = q2s[idx] % 2
            ab = (2 * rad, -2 * q) if side == 0 else (-2 * rad, 2 * (q + 1))
            flines.append((ab[0] + ab[1] * mid, idx))
        flines.sort(key=lambda x: (x[0], x[1]))
        return (K30, q2s, qzs, tuple(x[1] for x in flines))

    merged: List[Tuple[Q, Q, int, tuple]] = []
    for tile in hi_tiles:
        for aa, bb, lab in tile[2]:
            a, b = 50 * Q(aa), 50 * Q(bb)
            q_val = int(lab.removeprefix("joint"))
            key = tile_key(a, b)
            if merged and merged[-1][2] == q_val and merged[-1][3] == key:
                merged[-1] = (merged[-1][0], b, q_val, key)
            else:
                merged.append((a, b, q_val, key))

    out_tiles = []
    for a, b, q_val, key in merged:
        ln, ld = a.numerator, a.denominator
        rn, rd = b.numerator, b.denominator
        denom = ln * rd + rn * ld
        k30 = (2 * 30 * ld * rd) // denom
        assert k30 * rn <= 30 * rd and 30 * ld <= (k30 + 1) * ln
        assert q_val <= k30
        q2s = []
        for rad in RADII:
            v = (2 * (2 * rad) * ld * rd) // denom
            assert v * rn <= (2 * rad) * rd and (2 * rad) * ld <= (v + 1) * ln
            q2s.append(v)
        z40 = (2 * 40 * ld * rd) // denom
        z41 = (2 * 41 * ld * rd) // denom
        z43 = (2 * 43 * ld * rd) // denom
        for z, qz in ((40, z40), (41, z41), (43, z43)):
            assert qz * rn <= z * rd and z * ld <= (qz + 1) * ln
        vfact = sum(POLE_MULT[i] * q2s[i] for i in range(12)) - 2 * (3 * z40 + z41 + z43)

        perm = list(key[3])
        pts = [(0, 0)]
        for idx in perm:
            rad = RADII[idx]
            qr = q2s[idx] // 2
            ab = (2 * rad, -2 * qr) if q2s[idx] % 2 == 0 else (-2 * rad, 2 * (qr + 1))
            pts.append(ab)
        pts.append((0, 1))
        for u, v in zip(pts, pts[1:]):
            assert u[0] * ld + u[1] * ln <= v[0] * ld + v[1] * ln
            assert u[0] * rd + u[1] * rn <= v[0] * rd + v[1] * rn

        pos = [0] * 12
        for rank_idx, rad_idx in enumerate(perm):
            pos[rad_idx] = rank_idx

        k25 = q2s[7] // 2
        q30 = q2s[10] // 2
        s30 = q2s[10] % 2
        pos30 = pos[10]
        caps = [[0, 0] for _ in range(19)]
        for g in range(13):
            u, v = pts[g], pts[g + 1]
            w0, w1 = v[0] - u[0], v[1] - u[1]
            if w0 == 0 and w1 == 0:
                continue

            def delta_at(idx: int) -> int:
                q2 = q2s[idx]
                qr = q2 // 2
                lt = (g <= pos[idx])
                return 2 * qr + (1 if lt else 0) if q2 % 2 == 0 else 2 * qr + (1 if lt else 2)

            Np = sum(POLE_MULT[i] * delta_at(i) for i in range(12))
            Nz = 5 * delta_at(11) - (delta_at(8) + delta_at(9) + 3 * delta_at(10))
            lt30 = (g <= pos30)
            f30_plus = q30 + (1 if (s30 == 1 and not lt30) else 0)
            f30_minus = q30 - (1 if (s30 == 0 and not lt30) else 0)
            hist = [0] * 19
            for m in range(0, k25 + 1):
                mk = 0
                for i in range(8):
                    qr = q2s[i] // 2
                    sr = q2s[i] % 2
                    if m < qr or (m == qr and (sr == 1 or g <= pos[i])):
                        mk += POLE_MULT[i]
                if mk > 0:
                    right = m + f30_plus
                    left = f30_minus - m
                    base_val = vfact + Nz - (Np - mk)
                    for cost in refined_slots(mk, base_val, Np - mk, Nz, right, left):
                        hist[min(cost, 18)] += 1
            for m in range(1, k25 + 2):
                mk = 0
                for i in range(8):
                    qr = q2s[i] // 2
                    sr = q2s[i] % 2
                    if m <= qr or (m == qr + 1 and sr == 1 and pos[i] < g):
                        mk += POLE_MULT[i]
                if mk > 0:
                    right = m + f30_minus
                    left = f30_plus - m
                    base_val = vfact + Nz - (Np - mk)
                    for cost in refined_slots(mk, base_val, Np - mk, Nz, right, left):
                        hist[min(cost, 18)] += 1
            jc = hist_joint_caps(hist, q_val)
            for j in range(1, 19):
                if jc[j]:
                    caps[j][0] += jc[j] * w0
                    caps[j][1] += jc[j] * w1

        p0 = 30 * (k30 - q_val)
        p1 = -sum(range(q_val + 1, k30 + 1))
        per_ceil = aff_int_ceil(p0, p1, ln, ld, rn, rd, CERT_DEN)
        cap_ceil = sum(cap_int_ceil(caps[j][0], caps[j][1], ln, ld, rn, rd, CERT_DEN) for j in range(1, 19))
        u_num = per_ceil + cap_ceil
        out_tiles.append(dict(
            ln=ln, ld=ld, rn=rn, rd=rd,
            q=q_val, perm=perm, uNum=u_num,
        ))
    return out_tiles


def write_periodic_shards(pieces: List[dict], out_dir: Path, n_shards: int = 4, mini_size: int = 40) -> Tuple[int, int]:
    out_dir.mkdir(parents=True, exist_ok=True)
    total_f = 0
    total_c = 0
    chunk = (len(pieces) + n_shards - 1) // n_shards
    for s in range(n_shards):
        sl = pieces[s * chunk : min((s + 1) * chunk, len(pieces))]
        assert sl
        startN, startD = sl[0]["ln"], sl[0]["ld"]
        endN, endD = sl[-1]["rn"], sl[-1]["rd"]
        f_tot = sum(p["fbarNum"] for p in sl)
        c_tot = sum(p["c0Num"] for p in sl)
        total_f += f_tot
        total_c += c_tot
        lines = [
            "import OddZetaSix.SixFoldedCertCore",
            "",
            "set_option autoImplicit false",
            "set_option Elab.async false",
            "",
            f"namespace OddZetaSix.PeriodicData.Shard{s}",
            "open OddZetaSix.CertCore",
            "",
        ]
        # Split into mini-chunks of `mini_size` so each `decide +kernel` runs in < 2s with tiny memory!
        minis = [sl[i : i + mini_size] for i in range(0, len(sl), mini_size)]
        for mi, sub in enumerate(minis):
            m_sN, m_sD = sub[0]["ln"], sub[0]["ld"]
            m_eN, m_eD = sub[-1]["rn"], sub[-1]["rd"]
            m_f = sum(p["fbarNum"] for p in sub)
            m_c = sum(p["c0Num"] for p in sub)
            lines.append(f"private def chunk{mi} : List PeriodicPiece := [")
            for idx, p in enumerate(sub):
                comma = "," if idx + 1 < len(sub) else ""
                perm_str = "[" + ", ".join(str(x) for x in p["perm"]) + "]"
                lines.append(
                    f"  ⟨{p['ln']}, {p['ld']}, {p['rn']}, {p['rd']}, {perm_str}, "
                    f"{p['a0']}, {p['a1']}, {p['fbarNum']}, {p['c0Num']}⟩{comma}"
                )
            lines.extend([
                "]",
                f"private theorem chunk{mi}_valid : checkPeriodicShard {m_sN} {m_sD} {m_eN} {m_eD} {m_f} {m_c} chunk{mi} = true := by decide +kernel",
                "",
            ])
        # Combine mini-chunks step by step with left-associated `++` so unification is O(1)
        expr_list = "chunk0"
        for mi in range(1, len(minis)):
            expr_list = f"({expr_list} ++ chunk{mi})"
        lines.append(f"def shard{s}Pieces : List PeriodicPiece := {expr_list}")
        lines.append(f"def shard{s}FbarTotal : Nat := {f_tot}")
        lines.append(f"def shard{s}C0Total : Nat := {c_tot}")
        lines.append("")
        lines.append(f"theorem shard{s}_valid :")
        lines.append(f"    checkPeriodicShard {startN} {startD} {endN} {endD} shard{s}FbarTotal shard{s}C0Total shard{s}Pieces = true := by")
        lines.append(f"  unfold shard{s}Pieces shard{s}FbarTotal shard{s}C0Total")
        lines.append("  have h0 := chunk0_valid")
        acc_f = sum(p["fbarNum"] for p in minis[0])
        acc_c = sum(p["c0Num"] for p in minis[0])
        for mi in range(1, len(minis)):
            mf = sum(p["fbarNum"] for p in minis[mi])
            mc = sum(p["c0Num"] for p in minis[mi])
            acc_f += mf
            acc_c += mc
            meN, meD = minis[mi][-1]["rn"], minis[mi][-1]["rd"]
            lines.append(f"  have h{mi} := checkPeriodicShard_append_eq (f3 := {acc_f}) (c3 := {acc_c}) rfl rfl h{mi-1} chunk{mi}_valid")
        lines.append(f"  exact h{len(minis)-1}")
        lines.extend([
            "",
            f"end OddZetaSix.PeriodicData.Shard{s}",
            "",
        ])
        (out_dir / f"Shard{s}.lean").write_text("\n".join(lines), encoding="utf-8")
        print(f"  Wrote PeriodicData/Shard{s}.lean: {len(sl)} pieces ({len(minis)} chunks), [{startN}/{startD}, {endN}/{endD}], fbar={f_tot}, c0={c_tot}")
    return total_f, total_c


def write_high_shards(tiles: List[dict], out_dir: Path, n_shards: int = 6, mini_size: int = 8) -> int:
    out_dir.mkdir(parents=True, exist_ok=True)
    total_u = 0
    chunk = (len(tiles) + n_shards - 1) // n_shards
    for s in range(n_shards):
        sl = tiles[s * chunk : min((s + 1) * chunk, len(tiles))]
        assert sl
        startN, startD = sl[0]["ln"], sl[0]["ld"]
        endN, endD = sl[-1]["rn"], sl[-1]["rd"]
        u_tot = sum(t["uNum"] for t in sl)
        total_u += u_tot
        lines = [
            "import OddZetaSix.SixFoldedCertCore",
            "",
            "set_option autoImplicit false",
            "set_option Elab.async false",
            "",
            f"namespace OddZetaSix.HighData.Shard{s}",
            "open OddZetaSix.CertCore",
            "",
        ]
        minis = [sl[i : i + mini_size] for i in range(0, len(sl), mini_size)]
        for mi, sub in enumerate(minis):
            m_sN, m_sD = sub[0]["ln"], sub[0]["ld"]
            m_eN, m_eD = sub[-1]["rn"], sub[-1]["rd"]
            m_u = sum(t["uNum"] for t in sub)
            lines.append(f"private def chunk{mi} : List HighTile := [")
            for idx, t in enumerate(sub):
                comma = "," if idx + 1 < len(sub) else ""
                perm_str = "[" + ", ".join(str(x) for x in t["perm"]) + "]"
                lines.append(
                    f"  ⟨{t['ln']}, {t['ld']}, {t['rn']}, {t['rd']}, {t['q']}, {perm_str}, {t['uNum']}⟩{comma}"
                )
            lines.extend([
                "]",
                f"private theorem chunk{mi}_valid : checkHighShard {m_sN} {m_sD} {m_eN} {m_eD} {m_u} chunk{mi} = true := by decide +kernel",
                "",
            ])
        expr_list = "chunk0"
        for mi in range(1, len(minis)):
            expr_list = f"({expr_list} ++ chunk{mi})"
        lines.append(f"def shard{s}Tiles : List HighTile := {expr_list}")
        lines.append(f"def shard{s}UTotal : Nat := {u_tot}")
        lines.append("")
        lines.append(f"theorem shard{s}_valid :")
        lines.append(f"    checkHighShard {startN} {startD} {endN} {endD} shard{s}UTotal shard{s}Tiles = true := by")
        lines.append(f"  unfold shard{s}Tiles shard{s}UTotal")
        lines.append("  have h0 := chunk0_valid")
        acc_u = sum(t["uNum"] for t in minis[0])
        for mi in range(1, len(minis)):
            mu = sum(t["uNum"] for t in minis[mi])
            acc_u += mu
            meN, meD = minis[mi][-1]["rn"], minis[mi][-1]["rd"]
            lines.append(f"  have h{mi} := checkHighShard_append_eq (u3 := {acc_u}) rfl h{mi-1} chunk{mi}_valid")
        lines.append(f"  exact h{len(minis)-1}")
        lines.extend([
            "",
            f"end OddZetaSix.HighData.Shard{s}",
            "",
        ])
        (out_dir / f"Shard{s}.lean").write_text("\n".join(lines), encoding="utf-8")
        print(f"  Wrote HighData/Shard{s}.lean: {len(sl)} tiles ({len(minis)} chunks), [{startN}/{startD}, {endN}/{endD}], uTotal={u_tot}")
    return total_u


def main() -> None:
    lean_dir = Path(__file__).resolve().parents[1]
    cert_path = lean_dir.parent / "zeta6_certificate.json"
    print("Building periodic pieces...")
    pieces = build_periodic_pieces()
    print(f"Total periodic pieces: {len(pieces)}")
    f_tot, c_tot = write_periodic_shards(pieces, lean_dir / "OddZetaSix" / "PeriodicData", n_shards=6)

    # Periodic upper bound check: (c_tot + f_tot * (1/11 + 1/(12*121))) / (50 * CERT_DEN)
    C0_cert = (Q(c_tot, CERT_DEN) + Q(f_tot, CERT_DEN) * (Q(1, 11) + Q(1, 12 * 121))) / 50
    print(f"C0_cert = {float(C0_cert):.8f} <= 552/1000? {C0_cert <= Q(552, 1000)}")
    assert C0_cert <= Q(552, 1000)

    print("Building flat high tiles...")
    tiles = build_high_tiles(cert_path)
    print(f"Total flat high tiles: {len(tiles)}")
    u_tot = write_high_shards(tiles, lean_dir / "OddZetaSix" / "HighData", n_shards=8)

    C1_cert = Q(u_tot, 750 * CERT_DEN)
    print(f"C1_cert = {float(C1_cert):.8f} <= 7206/1000? {C1_cert <= Q(7206, 1000)}")
    assert C1_cert <= Q(7206, 1000)

    eps = Q(1, 10000)
    tiny = Q(18, 50) * eps
    total_exact = tiny + C0_cert + C1_cert
    total_milestone = tiny + Q(552, 1000) + Q(7206, 1000)
    print(f"Tiny (eps=1/10000)   = {float(tiny):.8f}")
    print(f"Exact C0+C1+tiny     = {float(total_exact):.8f} < 194/25 (7.76)? {total_exact < Q(194, 25)}")
    print(f"Milestone sum        = {float(total_milestone):.8f} < 194/25 (7.76)? {total_milestone < Q(194, 25)}")
    assert total_milestone < Q(194, 25)
    print("ALL SLIM ARITHMETIC CERTIFICATES GENERATED AND VERIFIED.")


if __name__ == "__main__":
    main()
