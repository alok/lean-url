# lean-url 

A library implementing URLs (aka URIs/IRIs) and their API according to the whatwg [URL spec](https://url.spec.whatwg.org) in [Lean 4](https://lean-lang.org/).

This library uses the term "URL" rather than "URI" for the same reason(s) as the whatwg spec: "URI and IRI are just confusing. In practice a single algorithm is used for both so keeping them distinct is not helping anyone. URL also easily wins the search result popularity contest."

## Status

IDNA/Punycode support has been implemented, bringing WPT test failures from 61 to 20 (67% improvement).

**Implemented:**
- Punycode encoder/decoder (RFC 3492)
- IDNA character mapping (fullwidth ASCII, mathematical alphanumerics, case folding)
- Unicode domain processing per WHATWG URL spec
- Strict UTF-8 validation in domain parsing

## TODO

+ Full IDNA compliance: Some edge cases in the IDNA mapping table are not yet covered.

+ Support for non-UTF8 encodings.

+ There is currently a significant amount of low hanging fruit in terms of efficiency gains.

+ Full Public Suffix List integration (currently uses simplified last-label algorithm).

## Examples:

```
import LeanUrl.Parser.Basic

open LeanUrl.Parser

-- URL parsing

/-
Except.ok {
  scheme := "http",
  username := some "user",
  password := some "pass",
  host := some (LeanUrl.Host.domain { val := "foo", h := _ }),
  port := some 21,
  path := Sum.inr #["bar;par"],
  query := some "b",
  fragment := some "c",
  blobUrlEntry := none
}
-/
#eval LeanUrl.Parser.parseUrl' "http://user:pass@foo:21/bar;par?b#c" (base := none)

/-
Except.ok {
  scheme := "http",
  username := some "user",
  password := some "pass",
  host := some (LeanUrl.Host.domain { val := "foo", h := _ }),
  port := some 21,
  path := Sum.inr #["bar;par"],
  query := some "b",
  fragment := some "c",
  blobUrlEntry := none
}
-/
#eval LeanUrl.Parser.parseUrl'
  (input := "http://user:pass@foo:21/bar;par?b#c")
  (base := some "http://example.org/foo/bar")

-- URL serialization

/-- info: Except.ok "file://host/C:" -/
#guard_msgs in #eval
  (parseUrl'
    (input := "C|")
    (base := "file://host/D:/dir1/dir2/file")
  ).map (fun url => url.serialize false)

/-- info: Except.ok "http://255.255.255.255/" -/
#guard_msgs in #eval
  (parseUrl'
    (input := "http://0xffffffff")
    (base := "http://other.com/")
  ).map (fun url => url.serialize false)
```




