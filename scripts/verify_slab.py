"""Independent exact scales, small finite cap controls and native Lean checks."""
from copy import deepcopy
from decimal import Decimal, localcontext
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import json
import os
import re
import subprocess
import sys

from verify import PIN, read_fraction, require, run_checked
from verify_tuned import arithmetic as check_tuned

ROOT = Path(__file__).resolve().parents[1]


def scale_constraints(d, k, cap_h_power, q_power, n_power, gamma):
    # s >= constant*q^2/H^cap_h_power, with H = 2h.
    losses = [2 + 2 * cap_h_power - q_power, 2 + cap_h_power - q_power,
              2 + 2 * cap_h_power - 2 * q_power]
    require(max(losses) <= 0, "zero-case growth")
    collision = 2 * gamma + 12 - d
    require(collision < 0, "collision deletion")
    pair = gamma + 12 * (6 - Fraction(3 * n_power, 2)) * (1 + q_power) * k - 6 * (k - 1)
    require(pair < 0, "pair deletion")
    return losses, collision, pair


def arithmetic(c, packing):
    previous, _, _ = check_tuned(packing)
    k = 1
    for _ in range(17):
        k *= 403
    require(c["schema"] == "heilbronn-slab-cap-v1", "schema")
    require(c["upstream_commit"] == PIN, "pin")
    require(c["status"] == "conditional-on-upstream-estimates", "status")
    require(c["scope"] == "paper exponent; not the upstream Lean comparator exponent", "scope")
    require(c["packing_certificate"] == "certificates/tuned.json", "packing path")
    require(c["packing_sha256"] == sha256((ROOT / "certificates/tuned.json").read_bytes()).hexdigest(),
            "packing hash")
    require(c["d"] == 13 and c["k"] == packing["k"] == str(k), "packing parameters")
    require(c["cap"] == {
        "set": "{(x,y,x^2-nu*y^2): 0 <= x < w, y in F_q}; nu nonsquare",
        "width": "w = floor(q/(1000*H^2))", "cardinality": "s = w*q",
        "density_bound": "s >= q^2/(2000*H^2)",
        "short_relation_change": "only first-coordinate bounds are required",
        "proof_status": "written finite-field argument; not formalized in Lean",
    }, "cap construction")
    scales = dict(packing["scales"])
    scales["q"] = "h^6 < q <= 2*h^6; q prime"
    require(c["scales"] == scales, "scales")
    # N^(3/2) = (hq)^6, q of order h^6, tau of order B^(k-1), B of order r^12.
    beta = Fraction(3 * 4 * (1 + 6) * k - (k - 1), 2)
    rho = 12 * beta
    gamma = rho / (2 * rho + 1)
    alpha = rho + gamma
    eta = 2 * gamma / alpha
    gain = eta / previous
    require(rho.denominator == 1 and c["rho"] == str(rho.numerator), "rho")
    for name, value in [("beta", beta), ("gamma", gamma), ("alpha", alpha), ("eta", eta),
                        ("gain_from_tuned", gain)]:
        require(read_fraction(c[name]) == value, name)
    require(0 < gamma < Fraction(1, 2), "sample growth")
    require(eta == Fraction(1, 498 * k + 7), "closed exponent")
    require(Fraction(215, 100) < gain < Fraction(216, 100), "gain enclosure")
    losses, collision, pair = scale_constraints(13, k, 2, 6, 4, gamma)
    con = c["constraints"]
    require(con["zero_case_h_powers"] == losses, "zero powers")
    require(read_fraction(con["collision_r_power"]) == collision, "collision power")
    require(read_fraction(con["pair_r_power"]) == pair, "pair power")
    require(con["cap_condition"] == "h >= 10 implies 2000*(2*h)^2 <= h^6 < q", "cap condition")
    require(10**4 >= 8000, "cap threshold")
    require(c["formal_scope"] == {
        "proved": ["existing finite packing and digit-moment inequalities via Tuned",
            "floor-width and slab-cardinality lower-bound arithmetic",
            "cap modulus and three zero-case inequalities",
            "cleared-denominator deletion inequalities and exponent identity",
            "215/100 < gain from tuned < 216/100"],
        "written_not_formalized": ["slab cap geometry and short-relation exclusion",
            "field norm, lattice, orbit and weighted counting estimates",
            "probability, asymptotic deletion and interpolation"],
    }, "formal scope")
    return eta, gain, gamma


def cap_points(q, w, nu):
    return [(x, y, (x*x - nu*y*y) % q) for x in range(w) for y in range(q)]


def check_cap(points, q, w):
    require(len(set(points)) == w * q, "cap cardinality")
    checked = 0
    for a, b, c in combinations(points, 3):
        u, v = [b[i] - a[i] for i in range(3)], [c[i] - a[i] for i in range(3)]
        require(any((u[i] * v[j] - u[j] * v[i]) % q for i, j in [(0, 1), (0, 2), (1, 2)]),
                "collinear triple")
        checked += 1
    return checked


def rejected(function, reason):
    try:
        function()
    except AssertionError as error:
        require(str(error) == reason, "wrong rejection: " + str(error))
    else:
        raise AssertionError("invalid control accepted: " + reason)


def finite_controls():
    caps = []
    for q, w in [(5, 1), (5, 3), (7, 2), (11, 3), (13, 4)]:
        squares = {x*x % q for x in range(q)}
        nu = next(x for x in range(1, q) if x not in squares)
        points = cap_points(q, w, nu)
        require(all(x < w for x, _, _ in points), "first coordinate")
        require(any(y >= w for _, y, _ in points), "uses coordinates outside cube")
        caps.append({"q": q, "w": w, "nu": nu, "points": len(points),
                     "triples_checked": check_cap(points, q, w)})
    rejected(lambda: check_cap(cap_points(5, 3, 1), 5, 3), "collinear triple")
    rejected(lambda: check_cap(cap_points(5, 3, 2)[:-1], 5, 3), "cap cardinality")

    shifts = []
    for q, H in [(2003, 1), (8009, 2)]:
        require(all(q % p for p in range(2, int(q**0.5) + 1)), "prime control modulus")
        w = q // (1000 * H * H)
        allowed = [a for a in range(q) if all(
            min(m*a % q, -m*a % q) > 3*H*w for m in range(1, 3*H + 1))]
        require(2 * len(allowed) >= q, "allowed-shift density")
        # Exhaust all first-coordinate right sides, including repeated points
        # and the larger coefficient box |x_i| <= H instead of a Euclidean ball.
        right_sides = {m: set() for m in range(-3*H, 3*H + 1) if m}
        for coefficients in product(range(-H, H + 1), repeat=3):
            m = sum(coefficients)
            if m:
                for v in product(range(w), repeat=3):
                    right_sides[m].add(-sum(x*y for x, y in zip(coefficients, v)) % q)
        comparisons = 0
        for a in allowed:
            require((-a) % q >= w, "zero exclusion")
            for m, rhs in right_sides.items():
                require(m*a % q not in rhs, "short nonzero-sum relation")
                comparisons += 1
        # Removing the first-coordinate restriction admits zero after an
        # allowed shift: choose v=(-a1,0,(-a1)^2) on the full paraboloid.
        a1 = allowed[0]
        x = (-a1) % q
        v, a = (x, 0, x*x % q), (a1, 0, -x*x % q)
        require(x >= w and all((u+t) % q == 0 for u, t in zip(v, a)),
                "unrestricted-first-coordinate counterexample")
        shifts.append({"q": q, "H": H, "w": w, "allowed_first_coordinates": len(allowed),
                       "relation_membership_checks": comparisons})
    return {"caps": caps, "shifts": shifts,
            "negative_controls": ["square nu", "missing cap point", "unrestricted first coordinate"],
            "scope": "finite sanity checks; not a universal finite-field proof"}


def main():
    c = json.loads((ROOT / "certificates/slab.json").read_text(encoding="utf-8"))
    packing = json.loads((ROOT / "certificates/tuned.json").read_text(encoding="utf-8"))
    eta, gain, gamma = arithmetic(c, packing)
    k = int(c["k"])
    negative_scales = [
        ((13, k, 2, 5, 4, gamma), "zero-case growth"),
        ((13, k, 6, 6, 4, gamma), "zero-case growth"),
        ((11, k, 2, 6, 4, gamma), "collision deletion"),
        ((13, k, 2, 6, 3, gamma), "pair deletion"),
    ]
    for arguments, reason in negative_scales:
        rejected(lambda: scale_constraints(*arguments), reason)
    for field, value, reason in [
        ("k", str(k - 1), "packing parameters"),
        ("rho", str(498 * k + 5), "rho"),
        ("eta", {"numerator": "1", "denominator": str(498 * k + 6)}, "eta"),
        ("cap", {**c["cap"], "cardinality": "s = w^3/q"}, "cap construction"),
    ]:
        bad = deepcopy(c)
        bad[field] = value
        rejected(lambda: arithmetic(bad, packing), reason)
    finite = finite_controls()

    manifest = json.loads((ROOT / "upstream/manifest.json").read_text(encoding="utf-8-sig"))
    require(manifest["commit"] == PIN, "manifest pin")
    for item in manifest["files"]:
        data = (ROOT / item["path"]).read_bytes()
        require(sha256(data).hexdigest() == item["sha256"] and len(data) == item["bytes"],
                "changed upstream: " + item["path"])
    version = run_checked(["lean", "--version"]).strip()
    require("version 4.11.0," in version, "Lean version")
    outputs = []
    for name in ["Sphere", "Tuned", "Slab"]:
        source = (ROOT / f"lean/{name}.lean").read_text(encoding="utf-8")
        require(not re.search(r"\b(sorry|admit|axiom|unsafe|native_decide)\b", source), "proof escape")
        compiled = subprocess.run(["lean", "-o", f"lean/{name}.olean", f"lean/{name}.lean"],
            cwd=ROOT, text=True, encoding="utf-8", errors="replace", capture_output=True,
            timeout=30, env={**os.environ, "LEAN_PATH": str(ROOT / "lean")})
        output = compiled.stdout + compiled.stderr
        require(compiled.returncode == 0, "Lean failure:\n" + output)
        outputs.append(output)
    audit = "".join(outputs)
    require("sorryAx" not in audit and "error:" not in audit, "incomplete formal proof")
    for name in ["slab_width_bound", "slab_size_bound", "cap_modulus", "zero_case_bounds",
                 "alteration_constraints", "exponent_identity", "slab_gain"]:
        require("'HeilbronnSlab." + name + "'" in outputs[-1], "missing axiom audit")
    require("'HeilbronnTuned.tuned_packing'" in audit, "missing packing audit")
    for entry in re.findall(r"depends on axioms: \[([^]]*)\]", audit):
        require(set(entry.split(", ")) <= {"propext", "Classical.choice", "Quot.sound"},
                "unexpected axiom")
    patch = ROOT / "patches/slab-cap.patch"
    run_checked(["git", "apply", "--check", "--directory=upstream/manuscript", str(patch)])
    require(patch.read_text(encoding="utf-8").count("\n+++ b/") == 6, "patch section coverage")
    evidence = ["lean/Sphere.lean", "lean/Tuned.lean", "lean/Slab.lean", "lean-toolchain",
        "scripts/build_slab.py", "scripts/verify_slab.py", "scripts/build_tuned.py",
        "scripts/verify_tuned.py", "scripts/build_sphere.py", "scripts/build_patch.py",
        "scripts/verify.py", "scripts/verify_sphere.py", "certificates/tuned.json",
        "certificates/slab.json", "patches/slab-cap.patch", "notes/sphere-packing.tex",
        "README.md", "docs/review.md", "upstream/manifest.json", "artifacts/sphere-latex-status.json"]
    with localcontext() as ctx:
        ctx.prec = 40
        decimal = lambda f: format(Decimal(f.numerator) / Decimal(f.denominator), ".14E")
        report = {
            "status": "pass", "python": sys.version, "lean": version, "upstream_commit": PIN,
            "source_files_verified": len(manifest["files"]),
            "eta_approx": decimal(eta), "gain_from_tuned_approx": decimal(gain),
            "scale_negative_controls": [{"d": a[0], "cap_h_power": a[2], "q_power": a[3],
                                         "n_power": a[4], "reason": r}
                                        for a, r in negative_scales],
            "negative_control_scope": "failure of stated sufficient bounds, not impossibility",
            "arithmetic_negative_controls": 4, "finite_controls": finite,
            "lean_axiom_audit": audit.splitlines(), "patch_applies": True, "patched_sections": 6,
            "evidence_sha256": {p: sha256((ROOT / p).read_bytes()).hexdigest() for p in evidence},
            "not_established": ["Lean proof of the slab cap geometry or full geometric theorem",
                "complete independent audit of upstream estimates",
                "practical finite-n improvement", "novelty, priority or global optimality"],
        }
    (ROOT / "artifacts/slab-verification.json").write_text(
        json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps({key: report[key] for key in
        ["status", "eta_approx", "gain_from_tuned_approx", "finite_controls", "patched_sections"]}, indent=2))


if __name__ == "__main__":
    main()
