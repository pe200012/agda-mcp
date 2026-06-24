"""End-to-end smoke test driving the real MCP tool functions against Agda.

Run: python test_server.py   (needs `agda` on PATH). Asserts loudly on failure.
"""
import asyncio, os, tempfile, time, shutil
import agda_mcp_py.server as S

SRC = """\
module {mod} where

data Nat : Set where
  zero : Nat
  suc  : Nat → Nat

foo : Nat
foo = ?

plus : Nat → Nat → Nat
plus = ?

bar : Nat
bar = ?
"""


async def main():
    d = tempfile.mkdtemp()
    path = os.path.join(d, "Demo.agda")
    with open(path, "w", encoding="utf-8") as f:
        f.write(SRC.format(mod="Demo"))

    # 1. load (and time it — the old code paid a ~1s timeout per call)
    t0 = time.time()
    r = await S.agda_load(path)
    dt = time.time() - t0
    print(f"[load {dt:.2f}s] {r}")
    assert "Loaded" in r and "3 goal" in r, r

    # 2. goals with types in one call (fix #3)
    g = await S.agda_get_goals()
    print("[goals]\n" + g)
    assert "?0 : Nat" in g and "Nat → Nat → Nat" in g, g

    # latency sanity: a trivial query shouldn't take ~1s of dead timeout
    t0 = time.time(); await S.agda_get_goals(); q = time.time() - t0
    print(f"[goals latency {q:.2f}s]")
    assert q < 0.8, f"query too slow ({q:.2f}s) — sync model regressed"

    # 3. auto on a single goal (fix #2) — solves foo with `zero`
    r = await S.agda_auto(0)
    print(f"[auto ?0] {r}")
    assert "Filled ?0" in r, r
    assert "foo = zero" in open(path).read(), "auto edit not applied"

    # 4. quoting safety (fix #4): give an expr with parens/spaces
    r = await S.agda_give(2, "suc (suc zero)")
    print(f"[give ?2] {r}")
    assert "Filled ?2" in r, r
    assert "bar = suc (suc zero)" in open(path).read(), "give edit wrong"

    # 5. intro on the remaining function goal -> lambda
    await S.agda_get_goals()
    r = await S.agda_intro(1)
    print(f"[intro ?1] {r}")
    assert "Filled ?1" in r and "λ" in r, r

    # 6. error path returns a message, doesn't hang/crash
    r = await S.agda_give(1, "this is not valid agda !!!")
    print(f"[bad give] {r[:80]}")
    assert "Error" in r, r

    # 7. case split on a fresh file
    path2 = os.path.join(d, "Split.agda")
    with open(path2, "w", encoding="utf-8") as f:
        f.write("module Split where\n\ndata Nat : Set where\n  zero : Nat\n  suc : Nat → Nat\n\nf : Nat → Nat\nf n = ?\n")
    await S.agda_load(path2)
    r = await S.agda_case_split(0, "n")
    print(f"[case split] {r}")
    assert "Case split" in r and "f zero" in open(path2).read(), r

    # 8. outline — token-cheap skeleton, no Agda round-trip
    ol = await S.agda_outline(path)
    print("[outline]\n" + ol)
    assert "foo : Nat" in ol and "data Nat : Set where" in ol, ol

    # 9. run_code — ephemeral standalone type-check
    ok = await S.agda_run_code("data Nat : Set where\n  zero : Nat\n\nx : Nat\nx = zero")
    print(f"[run_code ok] {ok[:40]!r}")
    assert ok.startswith("OK"), ok
    bad = await S.agda_run_code("x : DoesNotExist\nx = nope")
    print(f"[run_code bad] {bad[:60]!r}")
    assert "OK" not in bad and bad, bad

    # 10. agda_try — non-destructive candidate testing (file must stay untouched)
    path3 = os.path.join(d, "Try.agda")
    with open(path3, "w", encoding="utf-8") as f:
        f.write("module Try where\n\ndata Nat : Set where\n  zero : Nat\n  suc : Nat → Nat\n\nfoo : Nat\nfoo = ?\n")
    await S.agda_load(path3)
    before = open(path3).read()
    t = await S.agda_try(0, ["bogus thing", "zero", "suc ?"])
    print("[try give]\n" + t)
    assert "✗ bogus thing" in t, t
    assert "✓ zero  → solves goal" in t, t
    assert "✓ suc ?  → leaves 1 hole(s): Nat" in t, t          # sub-goal reporting
    assert open(path3).read() == before, "agda_try must not edit the file"

    # refine mode: `suc` auto-inserts a hole -> leaves a Nat sub-goal
    tr = await S.agda_try(0, ["suc"], refine=True)
    print("[try refine]\n" + tr)
    assert "✓ suc  → leaves 1 hole(s): Nat" in tr, tr
    assert open(path3).read() == before, "agda_try (refine) must not edit the file"

    # 11. Unicode + per-goal queries (regression for 3 dogfooding bugs):
    #     (a) sending Unicode expressions must not be \uXXXX-escaped,
    #     (b) agda_get_goal_type must read goalInfo.type,
    #     (c) agda_get_context must read context[].binding.
    path4 = os.path.join(d, "Uni.agda")
    with open(path4, "w", encoding="utf-8") as f:
        f.write("module Uni where\n\ndata ℕ : Set where\n  zero : ℕ\n  suc : ℕ → ℕ\n\n"
                "f : ℕ → ℕ\nf n = ?\n\ng : ℕ → ℕ\ng = ?\n")
    await S.agda_load(path4)
    gt = await S.agda_get_goal_type(0)
    print(f"[goal_type] {gt}")
    assert gt.strip() == "?0 : ℕ", gt                          # bug (b)
    ctx = await S.agda_get_context(0)
    print(f"[context]\n{ctx}")
    assert "n : ℕ" in ctx, ctx                                  # bug (c)
    ut = await S.agda_try(1, ["λ x → x", "λ x → suc x"])        # bug (a): Unicode send
    print(f"[unicode try]\n{ut}")
    assert "✓ λ x → x" in ut and "✓ λ x → suc x" in ut, ut
    r = await S.agda_give(1, "λ x → suc x")
    print(f"[unicode give] {r}")
    assert "Filled" in r and "g = λ x → suc x" in open(path4, encoding="utf-8").read(), r

    # 12. Unsolved metavariables must be reported (they hide in invisibleGoals,
    #     not visibleGoals — a file with them isn't fully checked).
    path5 = os.path.join(d, "Meta.agda")
    with open(path5, "w", encoding="utf-8") as f:
        f.write("module Meta where\npostulate A : Set\nfoo : A\nfoo = _\n")
    r = await S.agda_load(path5)
    print(f"[unsolved] {r}")
    assert "0 goal" in r and "unsolved metavariable" in r, r

    S.repl.stop()
    shutil.rmtree(d, ignore_errors=True)
    print("\nALL PASSED")


if __name__ == "__main__":
    asyncio.run(main())
