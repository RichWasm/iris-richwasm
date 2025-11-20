(lang dune 3.20)
(using coq 0.10)

(name iris-richwasm)
(version 0.1)

(generate_opam_files true)
(source (github RichWasm/iris-richwasm))

(package
  (name iris-richwasm)
  (depends
    iris-wasm
    (coq-record-update (>= 0.3.6))
    (core_unix (>= 0.17.1))
    (ppx_expect (>= 0.17.3))
    (ppx_import (>= 1.11.0))
    (ppx_jane (>= 0.17.0))
    (ppx_let (>= 0.17.0))
    (ppx_variants_conv (>= 0.17.1))
    (rocq-autosubst-ocaml (>= 1.1+9.0))
    (sexplib (>= 0.17.0)))
  (synopsis "RichWasm formalization in Coq and Iris")
  (description "RichWasm formalization in Coq based on Iris-Wasm.")
  (maintainers
    "Ryan Doenges"
    "Brianna Marshall")
  (authors
    "Ryan Doenges"
    "Brianna Marshall"
    "Maxime Legoupil"
    "Amal Ahmed"))
