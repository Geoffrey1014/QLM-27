# Bug schemas

In the compositional cells (C2, C3), the first stage asks the LLM to read the seed patch
and fill in a bug schema, which then guides PoC construction (C3 only) and query planning.
This directory holds the schema definition and the 125 schema instances saved by the C3
runs (25 seeds × 5 repeats); RQ4's single-shot point (L2) reuses these runs. C2 did not
save its schema as a separate file.

## Schema

Every pattern uses the same four slots. The stage-1 prompt (`code/prompts/C3-prompt.md`,
Stage 1) asks for one JSON document with these keys:

| Key | Meaning |
|---|---|
| `target_api` | the operation at the heart of the bug |
| `post_operation` | what the fix adds or changes after that operation |
| `critical_variable` | the program object the obligation applies to |
| `path_conditions` | the execution paths on which the bug manifests |
| `fits_pattern` | whether the patch fits the pattern under study; if `false`, the generation stops |
| `bug_type`, `cwe` | short label and CWE for the bug |

The slots were defined for resource leaks ("acquire → use → release"). For the other
three families the LLM reads them by analogy. The table below shows how the slots were
actually filled; each example is taken from the instance file named in brackets.

| Slot | resource-leak (`four-features-Lin`, `four-features-Lu`) | missing-check | delay-gfp | error-return |
|---|---|---|---|---|
| `target_api` | call that obtains a resource: `of_parse_phandle` [lin-1-rep1], `sctp_unpack_cookie` [lu-1-rep1] | call whose result can fail: `regmap_bulk_read` [mc-1-rep1], `kzalloc` [mc-2-rep1] | busy-wait or allocation call: `mdelay` [dgfp-1-rep1] | call that can fail: `platform_get_drvdata` [err-1-rep1] |
| `post_operation` | the release: `of_node_put`, `sctp_association_free` | a check of the result before use | replace with a sleeping primitive (`msleep`, or `GFP_KERNEL` for `GFP_ATOMIC`) | assign an error code to the return variable |
| `critical_variable` | variable holding the resource: `state_node`, `new_asoc` | variable holding the result: `priv->pFirmware` | the delay call or its GFP flag | the function's return variable: `err` |
| `path_conditions` | exits after the acquire that skip the release | uses of the result before or without a check | the function runs only in sleepable context | error branches that leave without setting the return variable |

## Instances

`instances/<seed>-rep<k>.json` is the stage-1 output of C3 generation `<seed>`, repeat
`<k>`, unchanged. Seed IDs match `data/seeds/` and `data/generated-queries/C3/`. All 125
instances have `fits_pattern = true`. Some instances add free-form keys (`notes`,
`rationale`, `pattern`) beyond the requested ones.
