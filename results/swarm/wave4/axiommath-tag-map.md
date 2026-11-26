## Your task: `wave4/axiommath-tag-map`

Goal: for **every** Stacks Project tag cited in the current GL26 and LP26 manuscripts (the manuscripts as they then were in the repository; they have since been removed from it; links `stacks.math.columbia.edu/tag/XXXX`; 141 tags in GL26, 18 in LP26, 150 distinct), record what AxiomMath/Stacks provides. **No Lean build is needed.** Output: one new file `results/AXIOMMATH_TAGS.md`, plus the script you use under `scripts/axiommath/` (you may add files there). Branch `wave4/axiommath-tag-map`: start with `git fetch --depth=50 origin formalization && git checkout -B wave4/axiommath-tag-map origin/formalization`.

Per tag, one row:

| tag | where GL26/LP26 cite it (result number + TeX label, or section) | what the paper uses it for (one line, your words) | AxiomMath declaration(s) carrying `@[stacks TAG ...]` or `add_to_stacks TAG` (full name, StacksCore/StacksFrontier) | scope (whole tag / part, with the attribute's comment / special case) | for spaces or only schemes (the paper always needs the algebraic-space version unless it applies the tag to schemes) | verdict: **usable** (the declaration states what the paper uses, for spaces) / **partial** / **schemes only** / **absent** |

Then a summary: counts by verdict, and the list of tags that are absent or schemes-only but needed for spaces, grouped by the GL26/LP26 result that needs them. 18 tags have no `@[stacks]` attribute in AxiomMath at all (003S 0118 03BT 03DH 03HA 03I7 03LT 04JA 04K7 04LX 05W7 0735 08FH 08G4 08J7 0E4V 0E5K 0EMV); for each, check whether it is a definition/section tag that AxiomMath covers under another tag or untagged, and what the paper needs from it.

Also cross-check `results/ASSUMPTIONS.md`: for each `S` row (Stacks input carried as a `Prop` in `RelativeFM.StacksInterface` or elsewhere), name the AxiomMath declaration that would discharge it once AxiomMath is imported, and whether the repo's `Prop` matches it (same statement, weaker, stronger, or different model). Report in a second table; do not edit `ASSUMPTIONS.md`.

Read declarations, not only names: the scope and spaces-vs-schemes columns must come from the Lean signature.
