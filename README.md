# GitHub Core Clone v2

A one-process Git forge in a single stdlib-only Python file: git smart HTTP
(v2 + v0), a GitHub-compatible REST v3 API, GraphQL, and MCP over one
content-addressed object store.

v2 is a from-scratch rewrite for speed: a raw-socket HTTP server with
keep-alive, lock-free reads over the immutable object store, and a pack cache
keyed by (repo generation, wants, haves, shallow set) so concurrent clones
build each pack once. Passes the sealed conformance suite 120/120 and runs
every benchmark workload roughly 2-3x faster than v1 in paired local runs.

Run: `python3 main.py`
