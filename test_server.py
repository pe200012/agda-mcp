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

    S.repl.stop()
    shutil.rmtree(d, ignore_errors=True)
    print("\nALL PASSED")


if __name__ == "__main__":
    asyncio.run(main())
