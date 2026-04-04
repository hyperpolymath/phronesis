# Test Requirements — Phronesis

## CRG Grade: C — ACHIEVED 2026-04-04

All CRG C requirements are met:

| Category | File(s) | Status |
|----------|---------|--------|
| Unit tests | `test/lexer_test.exs`, `test/parser_test.exs`, `test/compiler_test.exs`, etc. | PASS |
| Smoke tests | `test/phronesis_test.exs` | PASS |
| P2P / property-based | `test/property_test.exs` (StreamData, 5 properties) | PASS (2026-04-04) |
| E2E / reflexive | `test/e2e_test.exs` (6 full-pipeline tests) | PASS (2026-04-04) |
| Aspect tests | `test/fuzz/lexer_fuzz_test.exs`, `test/fuzz/parser_fuzz_test.exs` | PASS |
| Contract tests | `test/conformance_test.exs`, `test/type_checker_test.exs` | PASS |
| Benchmarks | `bench/bench_lexer.exs`, `bench/bench_parser.exs` (Benchee) | BASELINED |

## Notes

- `stream_data ~> 1.0` added to `mix.exs` `:test` deps for property tests.
- `lib/phronesis/incremental_parser.ex` fixed: `after` reserved word renamed to `after_text`.
- Fuzz tests in `test/fuzz/` serve as aspect tests (panic-freedom, output hygiene).
- Benchmarks are already present via Benchee — run with `mix run bench/bench_lexer.exs`.

## Running Tests

```bash
mix test                          # all unit + property + E2E tests
mix run bench/bench_lexer.exs     # lexer benchmark
mix run bench/bench_parser.exs    # parser benchmark
FUZZ_ITERATIONS=100000 mix test test/fuzz/  # fuzz suite
```
