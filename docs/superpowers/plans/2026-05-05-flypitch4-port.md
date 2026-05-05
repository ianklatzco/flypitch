# Flypitch Lean 4 Port Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Produce a working Lean 4 artifact at `flypitch4/` whose top-level theorem `independence_of_CH` matches the Lean 3 result in `src/summary.lean`, with `#print axioms` showing only the standard kernel axioms (`propext`, `Classical.choice`, `Quot.sound`).

**Architecture:** File-by-file LLM-assisted port in dependency order from leaves (`to_mathlib`) up to `summary`. Each file follows a fixed protocol: (1) stub the public API as `sorry`'d declarations, (2) build the stub green, (3) fill in proofs declaration-by-declaration, (4) drop any helpers already upstreamed into mathlib4. Cached mathlib4 oleans mean per-file rebuilds are seconds, not minutes.

**Tech Stack:** Lean 4 v4.30.0-rc2, mathlib4 (master, pinned in `flypitch4/lake-manifest.json`), Lake build system. Reference Lean 3 source in `src/`.

---

## Conventions (apply to every file-port task)

### Source layout

| Lean 3 (reference) | Lean 4 (port) |
|---|---|
| `src/<snake_name>.lean` | `flypitch4/Flypitch4/<PascalName>.lean` |
| `src/to_mathlib.lean` | `flypitch4/Flypitch4/ToMathlib.lean` |
| `src/pSet_ordinal.lean` | `flypitch4/Flypitch4/PSetOrdinal.lean` |
| `src/bv_tauto.lean` | `flypitch4/Flypitch4/BvTauto.lean` |
| `src/bvm_extras2.lean` | `flypitch4/Flypitch4/BvmExtras2.lean` |
| `src/set_theory.lean` | `flypitch4/Flypitch4/SetTheoryExt.lean` (renamed to avoid namespace shadowing of `Mathlib.SetTheory`) |

The root module `flypitch4/Flypitch4.lean` accumulates `import Flypitch4.<PascalName>` lines as files land.

### Per-file porting protocol

For each Lean 3 source file `<X>.lean`:

1. **Read the Lean 3 source in full.** Make notes (in the agent's context, not on disk) of: namespace structure, declarations exported, mathlib3 imports, tactics used heavily.

2. **Determine the public API.** The "public API" is the set of symbols that *downstream* flypitch files use from this file. Find them with:
   ```
   for sym in $(grep -oE '^(theorem|lemma|def|instance|structure|class) +[A-Za-z_][A-Za-z0-9_'"'"']*' src/<X>.lean | awk '{print $2}'); do
     hits=$(grep -lE "\\b$sym\\b" src/*.lean | grep -v "src/<X>.lean" | wc -l)
     [ "$hits" -gt 0 ] && echo "$sym  ($hits files)"
   done
   ```
   Symbols with zero downstream hits are private — skip stubbing them, port directly when filling in.

3. **Stub the public API as `sorry`'d declarations** in `flypitch4/Flypitch4/<PascalName>.lean`. Match Lean 3 names exactly (preserve snake_case if they're cross-file, otherwise update to Lean 4 idiom). Stubs look like:
   ```
   theorem foo_bar (x : α) : P x := sorry
   def baz : Nat := sorry
   ```

4. **Build the stub:**
   ```
   cd flypitch4 && PATH="$HOME/.elan/bin:$PATH" lake build Flypitch4.<PascalName>
   ```
   Expected: `Build completed successfully`, possibly with `sorry` warnings.

5. **Add the import to the root module.**
   ```
   echo 'import Flypitch4.<PascalName>' >> flypitch4/Flypitch4.lean
   cd flypitch4 && PATH="$HOME/.elan/bin:$PATH" lake build
   ```
   Expected: full project builds.

6. **Commit the stub:**
   ```
   git add flypitch4/Flypitch4/<PascalName>.lean flypitch4/Flypitch4.lean
   git commit -m "port: stub Flypitch4.<PascalName>"
   ```

7. **Fill in proofs declaration-by-declaration.** After every 5–10 declarations, rebuild. Each non-trivial declaration is a sub-step:
   - Read the Lean 3 statement and proof
   - Map mathlib3 names in the proof body to mathlib4 names (see "Mathlib3 → Mathlib4 mapping" below)
   - Translate tactic-mode syntax (`begin … end` → `by …`, semicolons → newlines, etc.)
   - Build the file. Fix errors before moving on.

8. **Drop already-upstreamed helpers.** When porting a `to_mathlib`-style helper, first search mathlib4 (see mapping below) for an existing version. If found: delete the declaration and rebind any flypitch caller to the mathlib4 name. Don't carry private versions of upstream lemmas.

9. **Verify final state:**
   - No `sorry` in the file: `grep -n sorry flypitch4/Flypitch4/<PascalName>.lean` returns nothing.
   - File builds clean: `lake build Flypitch4.<PascalName>` returns `Build completed successfully`.
   - Public API signatures match Lean 3 (see "Signature parity check" below).

10. **Commit the completed file:**
    ```
    git add flypitch4/Flypitch4/<PascalName>.lean
    git commit -m "port: complete Flypitch4.<PascalName>"
    ```

### Mathlib3 → Mathlib4 mapping strategy

Mathlib4 no longer ships the `mathlib3-port-status.yaml` file (the port is long complete and that scaffolding was removed). Use these techniques in order:

1. **Module path translation.** Mathlib3 dotted paths → mathlib4 PascalCase:
   - `data.set.countable` → `Mathlib.Data.Set.Countable`
   - `algebra.ordered_group` → `Mathlib.Algebra.Order.Group.Defs` (often split into `Defs`/`Lemmas`)
   - `order.complete_boolean_algebra` → `Mathlib.Order.CompleteBooleanAlgebra`
   - `set_theory.zfc` → `Mathlib.SetTheory.ZFC.Basic`
   - `set_theory.cofinality` → `Mathlib.SetTheory.Cardinal.Cofinality`
   - `order.zorn` → `Mathlib.Order.Zorn`
   - `order.bounded_lattice` → `Mathlib.Order.BoundedOrder` (renamed)

   When uncertain, find by content:
   ```
   cd flypitch4/.lake/packages/mathlib
   grep -lr "theorem <some_specific_lemma_from_old_module>" Mathlib/
   ```

2. **Symbol renaming.** Mathlib4 uses camelCase for most names, with namespace shuffling. When the build reports `unknown identifier 'foo_bar'`:
   ```
   cd flypitch4/.lake/packages/mathlib
   grep -rE "(theorem|lemma|def) +(foo_bar|fooBar|FooBar)" Mathlib/ | head
   ```
   Common rename patterns:
   - snake_case → camelCase (`mk_le_mk` → `mk_le_mk` is unchanged in some places, `is_open_inter` → `IsOpen.inter`, etc. — varies)
   - Dot-notation refactor: `set.subset.trans` → `Set.Subset.trans` or just `Subset.trans`
   - `cardinal.mk` → `Cardinal.mk`
   - `pSet` → `PSet`, `bSet` → `BSet`-ish (project-internal, but if mathlib has a similar concept under a different name, prefer it)

3. **API drift.** Some mathlib3 lemmas were generalized, weakened, or replaced. If a literal translation says "type mismatch" rather than "unknown identifier", read the mathlib4 docstring of the closest match and adapt. `exact?` and `apply?` tactics are useful here.

4. **Notation.** Lean 4 mathlib uses different notation for some things:
   - Set membership: same `∈`, but instances/coercions changed
   - Lattice top/bot: `⊤`/`⊥` unchanged but namespace-qualified differently
   - Cardinal arithmetic: roughly same notation

### Signature parity check

After completing each file, verify the public API matches Lean 3 by side-by-side:

```
diff <(grep -E '^(theorem|lemma|def) ' src/<X>.lean | sort) \
     <(grep -E '^(theorem|lemma|def) ' flypitch4/Flypitch4/<PascalName>.lean | sort)
```

Names should match (modulo casing and intentional drops to mathlib4). For the marquee theorems in `summary.lean` — `independence_of_CH`, `CH_unprovable`, `neg_CH_unprovable`, `godel_completeness_theorem`, `boolean_valued_soundness_theorem`, `fundamental_theorem_of_forcing`, `ZFC_is_consistent` — the *full signatures* must match exactly.

### Build / verification cadence

- **After every file port:** rebuild that file (`lake build Flypitch4.<PascalName>`).
- **After every 5 files ported:** full `lake build` (no target) to catch interaction issues.
- **After `summary` is ported:** the final acceptance check is
  ```
  cd flypitch4 && PATH="$HOME/.elan/bin:$PATH" lake env lean --run <(echo "import Flypitch4.Summary
  #print axioms independence_of_CH")
  ```
  Expected output: a list naming exactly `propext`, `Classical.choice`, `Quot.sound` (or a strict subset).

### When a file is hard

If a file resists translation for >30 minutes of compounding errors:
1. Stop. Re-stub the still-broken declarations as `sorry`. Commit the partial port.
2. Move on. Come back after more upstream files are done — sometimes the issue is a missing helper.
3. If a single declaration is truly stuck, leave it as `sorry` and add a `-- TODO: port from src/<X>.lean:LNUM` comment. Track these in the final integration task.

### Sub-checkpoints for huge files

Files >1000 lines (`to_mathlib` 1715, `fol` 2759, `pSet_ordinal` 1391, plus `bvm`/`bvm_extras` likely similar) need internal commits per logical section. Identify sections from `namespace`/`section` boundaries in the Lean 3 source and commit per section: `port: <PascalName> — <section name> section`.

---

## File order (24 files in `summary.lean`'s transitive closure)

Listed bottom-up by dependency level. Files at the same level are independent and can be ported in parallel sub-sessions.

| Level | Files | Notes |
|---|---|---|
| 0 | `to_mathlib`, `set_theory`, `bv_tauto`, `colimit` | Leaves; depend only on mathlib |
| 1 | `fol`, `pSet_ordinal` | Depend on `to_mathlib` |
| 2 | `bfol`, `compactness`, `regular_open_algebra`, `bvm` | |
| 3 | `language_extension`, `completion`, `cantor_space`, `bvm_extras`, `collapse` | |
| 4 | `henkin`, `bvm_extras2`, `forcing` | |
| 5 | `aleph_one`, `completeness` | |
| 6 | `forcing_CH`, `zfc` | |
| 7 | `print_formula` | |
| 8 | `summary` | Top |

Out-of-scope (not in summary's closure, port only if needed): `abel`, `abstract_forcing`, `normal`, `parse_formula`, `reflect_test`, `ring`, `zfc_expanded`.

---

## Tasks

### Task 0: Set up `Flypitch4/` subdirectory

**Files:**
- Create: `flypitch4/Flypitch4/.gitkeep`
- Modify: none yet

- [ ] **Step 1: Create the subdirectory**

```
mkdir -p flypitch4/Flypitch4
touch flypitch4/Flypitch4/.gitkeep
```

- [ ] **Step 2: Verify build still works**

```
cd flypitch4 && PATH="$HOME/.elan/bin:$PATH" lake build
```
Expected: `Build completed successfully (3 jobs)` (or equivalent — same as the post-bootstrap state).

- [ ] **Step 3: Commit**

```
git add flypitch4/Flypitch4/.gitkeep
git commit -m "port: scaffold Flypitch4/ subdirectory"
```

---

### Task 1: Port `to_mathlib.lean` (1715 lines)

**Files:**
- Reference: `src/to_mathlib.lean`
- Create: `flypitch4/Flypitch4/ToMathlib.lean`
- Modify: `flypitch4/Flypitch4.lean` (add `import Flypitch4.ToMathlib`)

**Lean 3 imports to map:**
- `algebra.ordered_group` → likely split across `Mathlib.Algebra.Order.Group.{Defs,Lemmas}`
- `data.set.disjointed` → `Mathlib.Order.Disjointed`
- `data.set.countable` → `Mathlib.Data.Set.Countable`
- `set_theory.cofinality` → `Mathlib.SetTheory.Cardinal.Cofinality`

**Special considerations:**
- This is a grab-bag of helper lemmas across `function`, `dvector`, `set`, `topological_space`, `ordinal`, `cardinal`, `nat`, `tactic.interactive`, `classical`, `list` namespaces.
- **Many declarations are likely already in mathlib4.** For each declaration, search mathlib4 first; if it exists, drop the declaration and rebind callers later.
- The `dvector` type (dependent vector of fixed length) is project-defined and probably needs to stay — but mathlib4 has `Vector` (Lean core) and `Mathlib.Data.Vector` which may suffice for most uses.
- Tactic extensions in `namespace tactic.interactive` need full rewrite for Lean 4's macro/elab system. Defer these — port them only when downstream files actually need them; many tactic helpers won't survive the port.

**Sub-checkpoints (commit per section):**
1. `function` namespace (~15 lines)
2. `dvector` namespace (~250 lines)
3. `set` namespace (~30 lines)
4. `topological_space` section (~50 lines)
5. `ordinal` namespace (~10 lines)
6. `cardinal` namespace (~50 lines)
7. `nat` namespace (~10 lines)
8. `classical` namespace (~10 lines)
9. `list` namespace (~end)
10. `tactic.interactive` section — defer; likely re-do in Lean 4 only as needed

- [ ] **Step 1: Read the Lean 3 source and inventory declarations**

```
wc -l src/to_mathlib.lean
grep -nE '^(namespace|section) ' src/to_mathlib.lean
grep -cE '^(theorem|lemma|def|instance|structure|class) ' src/to_mathlib.lean
```

- [ ] **Step 2: Identify the public API**

```
for sym in $(grep -oE '^(theorem|lemma|def|instance) +[A-Za-z_][A-Za-z0-9_'"'"']*' src/to_mathlib.lean | awk '{print $2}'); do
  hits=$(grep -lE "\\b$sym\\b" src/*.lean | grep -v "src/to_mathlib.lean" | wc -l)
  [ "$hits" -gt 0 ] && echo "$sym  ($hits files)"
done
```

Save the output mentally/in conversation — this is the stub list.

- [ ] **Step 3: Stub the public API**

Create `flypitch4/Flypitch4/ToMathlib.lean` with `sorry`'d versions of every public-API symbol identified in Step 2, plus the `dvector` definition. Imports at top: the four mathlib4 modules listed above. Each stub mirrors the Lean 3 type signature, with mathlib4 namespace adjustments.

- [ ] **Step 4: Build the stub**

```
cd flypitch4 && PATH="$HOME/.elan/bin:$PATH" lake build Flypitch4.ToMathlib
```
Expected: builds with `declaration uses 'sorry'` warnings.

- [ ] **Step 5: Wire to root module and commit stub**

```
echo 'import Flypitch4.ToMathlib' >> flypitch4/Flypitch4.lean
cd flypitch4 && PATH="$HOME/.elan/bin:$PATH" lake build
git add flypitch4/Flypitch4/ToMathlib.lean flypitch4/Flypitch4.lean
git commit -m "port: stub Flypitch4.ToMathlib"
```

- [ ] **Step 6–14: Fill in each section**

For each sub-checkpoint section (function, dvector, set, …): port the declarations, search mathlib4 to drop already-upstreamed ones, build, commit with message `port: ToMathlib — <section> section`.

- [ ] **Step 15: Final verification**

```
grep -n sorry flypitch4/Flypitch4/ToMathlib.lean   # should print nothing (or only deferred TODOs)
cd flypitch4 && PATH="$HOME/.elan/bin:$PATH" lake build Flypitch4.ToMathlib
diff <(grep -E '^(theorem|lemma|def) ' src/to_mathlib.lean | awk '{print $2}' | sort -u) \
     <(grep -E '^(theorem|lemma|def) ' flypitch4/Flypitch4/ToMathlib.lean | awk '{print $2}' | sort -u)
```
Differences should only be: declarations we intentionally dropped (now in mathlib4) or renamed for camelCase.

- [ ] **Step 16: Commit completion marker**

```
git commit --allow-empty -m "port: complete Flypitch4.ToMathlib"
```

---

### Task 2: Port `set_theory.lean` (713 lines)

**Files:**
- Reference: `src/set_theory.lean`
- Create: `flypitch4/Flypitch4/SetTheory.lean` — but note: this name collides with `Mathlib.SetTheory`. Use **`Flypitch4.SetTheoryExt`** instead to avoid namespace ambiguity in callers.
- Modify: `flypitch4/Flypitch4.lean`

**Lean 3 imports to map:** `.to_mathlib` only (already ported).

**Special considerations:**
- Project-defined helpers about set theory not in mathlib3 at the time. Many likely now exist in mathlib4 — search before porting each lemma.
- Used by: `regular_open_algebra` (Level 2).

**Steps:** follow the per-file protocol. Sub-checkpoint per `namespace`/`section` boundary.

---

### Task 3: Port `bv_tauto.lean` (94 lines)

**Files:**
- Reference: `src/bv_tauto.lean`
- Create: `flypitch4/Flypitch4/BvTauto.lean`
- Modify: `flypitch4/Flypitch4.lean`

**Lean 3 imports:** `.to_mathlib`.

**Special considerations:**
- Small file; likely a tactic for boolean-valued tautologies. If it's primarily tactic code (`namespace tactic.interactive`), the port is a Lean 4 macro/elab rewrite — non-trivial despite the line count. Read carefully before stubbing.
- Used by: `bvm`.

**Steps:** follow the per-file protocol. No sub-checkpoints needed — single commit at completion.

---

### Task 4: Port `colimit.lean` (250 lines)

**Files:**
- Reference: `src/colimit.lean`
- Create: `flypitch4/Flypitch4/Colimit.lean`
- Modify: `flypitch4/Flypitch4.lean`

**Lean 3 imports:** `.to_mathlib`.

**Special considerations:**
- Defines colimits of structures, used in the Henkin construction.
- mathlib4 has substantial category theory infrastructure (`Mathlib.CategoryTheory.Limits.*`) — check whether this file's purpose is now subsumed before porting verbatim.
- Used by: `henkin`.

**Steps:** follow the per-file protocol.

---

### Task 5: Port `fol.lean` (2759 lines — largest file)

**Files:**
- Reference: `src/fol.lean`
- Create: `flypitch4/Flypitch4/Fol.lean`
- Modify: `flypitch4/Flypitch4.lean`

**Lean 3 imports:** `.to_mathlib`.

**Special considerations:**
- The first-order logic deep embedding — the foundation of half the project. Defines `Language`, `preterm`, `preformula`, `term`, `formula`, `sentence`, `prf`, `provable`, `Theory`, `is_consistent`, `soundness`, etc. (these are the symbols `summary.lean` `#print`s).
- Heavy use of dependent types and `dvector`.
- Largest file in the closure — sub-checkpoint per `namespace` aggressively.
- Tactic-heavy proofs; expect to rewrite many `begin … end` blocks.
- Used by: `bfol`, `compactness`, `abel`, `parse_formula`, `reflect_test`, `ring`, `zfc_expanded`, `normal` — heavily depended-on.

**Sub-checkpoints (estimated from typical FOL embedding structure):**
1. `Language` definition + basic instances
2. `preterm` / `term`
3. `preformula` / `formula` / `sentence`
4. Substitution, lifting
5. `prf` / `provable` / proof system
6. `Theory` + `is_consistent`
7. Models / satisfaction
8. Soundness theorem
9. Misc helpers

**Steps:** follow the per-file protocol with aggressive sub-checkpointing — commit per namespace.

---

### Task 6: Port `pSet_ordinal.lean` (1391 lines)

**Files:**
- Reference: `src/pSet_ordinal.lean`
- Create: `flypitch4/Flypitch4/PSetOrdinal.lean`
- Modify: `flypitch4/Flypitch4.lean`

**Lean 3 imports:** `set_theory.zfc` (→ `Mathlib.SetTheory.ZFC.Basic`), `tactic.tidy` (no Lean 4 equivalent — replace with explicit tactics or `decide`/`aesop`), `.to_mathlib`.

**Special considerations:**
- Extends mathlib's `pSet` (pre-set hierarchy) with ordinal-indexed structure used to build the boolean-valued models.
- `tactic.tidy` is gone in Lean 4 — most usages can be replaced with `aesop` (modern equivalent) or hand-written proofs.
- Used by: `bvm`, `collapse`.

**Sub-checkpoints:** per namespace/section boundary.

---

### Tasks 7–23: Mid-stack ports

These follow the same protocol. Per-file specifics are deferred to the moment the task is started — by then upstream ports are done and the public API requirements are concrete.

For each, the agent should at task start:
1. Run `wc -l src/<name>.lean` and `grep -nE '^(namespace|section) ' src/<name>.lean` to gauge scope.
2. Run the public-API discovery script from the protocol.
3. Apply the per-file protocol with sub-checkpoints if >500 lines.

| Task | File | Lean 3 imports (with mathlib4 mapping) | Used by |
|---|---|---|---|
| 7 | `bfol` | `.fol`, `order.complete_boolean_algebra` (→ `Mathlib.Order.CompleteBooleanAlgebra`) | `zfc` |
| 8 | `compactness` | `.fol` | `completion`, `language_extension` |
| 9 | `regular_open_algebra` | `.set_theory`, `order.complete_boolean_algebra` | `cantor_space`, `collapse` |
| 10 | `bvm` | `order.complete_boolean_algebra`, `order.zorn` (→ `Mathlib.Order.Zorn`), `.pSet_ordinal`, `.bv_tauto` | `bvm_extras` |
| 11 | `language_extension` | `.compactness` | `henkin` |
| 12 | `completion` | `.compactness`, `order.zorn` | `henkin` |
| 13 | `cantor_space` | `.regular_open_algebra` | `forcing` |
| 14 | `bvm_extras` | `.bvm` | `bvm_extras2`, `forcing` |
| 15 | `collapse` | `.regular_open_algebra`, `.pSet_ordinal` | `forcing_CH` |
| 16 | `henkin` | `.completion`, `.language_extension`, `.colimit` | `completeness` |
| 17 | `bvm_extras2` | `.bvm_extras` | `aleph_one` |
| 18 | `forcing` | `.bvm_extras`, `.cantor_space` | `zfc` |
| 19 | `aleph_one` | `.bvm_extras2` | `forcing_CH` |
| 20 | `completeness` | `.henkin` | `summary` |
| 21 | `forcing_CH` | `.collapse`, `.aleph_one` | `zfc` |
| 22 | `zfc` | `.bfol`, `.forcing`, `.forcing_CH` | `print_formula`, `summary` |
| 23 | `print_formula` | `.zfc` | `summary` |

After each task, full `lake build` (no target) to catch surprises. After every 5 tasks, run all three `lake build` invocations as a stress check; commit a checkpoint marker `port: checkpoint after <name>`.

---

### Task 24: Port `summary.lean` (96 lines)

**Files:**
- Reference: `src/summary.lean`
- Create: `flypitch4/Flypitch4/Summary.lean`
- Modify: `flypitch4/Flypitch4.lean`

**Lean 3 imports:** `.zfc`, `.completeness`, `.print_formula` (all already ported by this point).

**Special considerations:**
- This is mostly `#print` statements (which become `#print` in Lean 4 too) and theorem restatements that defer to upstream proofs.
- The `#eval print_formula_list [...]` line uses the project-defined pretty-printer; if that infrastructure ported cleanly, this just works.
- The seven theorems at the bottom (`godel_completeness_theorem`, `boolean_valued_soundness_theorem`, `fundamental_theorem_of_forcing`, `ZFC_is_consistent`, `CH_unprovable`, `neg_CH_unprovable`, `independence_of_CH`) are the marquee API — their **signatures must match Lean 3 exactly** (modulo unicode variant: `⊢'`, `⊨`, etc.).
- The `independent` definition in `summary.lean:87` is local to summary.

- [ ] **Step 1: Read `src/summary.lean` end-to-end.** It's 96 lines.

- [ ] **Step 2: Stub `Flypitch4/Summary.lean`** with all seven marquee theorems as `sorry` and the `independent` definition.

- [ ] **Step 3: Build the stub.**
   ```
   cd flypitch4 && PATH="$HOME/.elan/bin:$PATH" lake build Flypitch4.Summary
   ```

- [ ] **Step 4: Fill in the proofs.** Each is a one-liner deferring to upstream (e.g. `independence_of_CH := And.intro CH_unprovable neg_CH_unprovable`).

- [ ] **Step 5: Match the `#print` and `#eval` statements** verbatim from Lean 3 (most should just work; some may need namespace prefixes).

- [ ] **Step 6: Final acceptance check.**

```
cd flypitch4 && PATH="$HOME/.elan/bin:$PATH" lake build
grep -rn sorry flypitch4/Flypitch4/   # must print nothing
```

Then in a Lean session:

```
cd flypitch4 && PATH="$HOME/.elan/bin:$PATH" lake env lean -- <(printf 'import Flypitch4.Summary\n#print axioms independence_of_CH\n')
```

Expected: lists only `propext`, `Classical.choice`, `Quot.sound` (or a strict subset).

- [ ] **Step 7: Side-by-side signature check.**

```
diff <(grep -E '^(theorem|def) ' src/summary.lean | sort) \
     <(grep -E '^(theorem|def) ' flypitch4/Flypitch4/Summary.lean | sort)
```

- [ ] **Step 8: Final commit.**

```
git add flypitch4/Flypitch4/Summary.lean flypitch4/Flypitch4.lean
git commit -m "port: complete Flypitch4.Summary — independence_of_CH proven in Lean 4"
```

---

## After completion

- Push to `origin/master`.
- Update `flypitch4/README.md` (create if absent) with: build instructions, mapping from Lean 3 source files to Lean 4 ports, and any deliberate divergences from the original.
- Sweep for `-- TODO: port from src/...` comments left during hard-file deferrals; address each.
- Run `lake build` from a fresh clone to confirm the cache + manifest survive a checkout.

## Out of scope

- Porting the 7 auxiliary files outside summary's closure (`abel`, `abstract_forcing`, `normal`, `parse_formula`, `reflect_test`, `ring`, `zfc_expanded`).
- Mechanical mathport scaffolding (decided against in favor of hand-port).
- Removing the original `src/` directory or `leanpkg.toml` — they remain as the Lean 3 reference.
- Submitting the port to mathlib4 as an extra; that's a separate downstream effort.
