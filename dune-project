(lang dune 3.16)
(using coq 0.9)

(name iris-richwasm)
(version 0.1)

(generate_opam_files true)
(source (github RichWasm/iris-richwasm))

(package
  (name iris-richwasm)
  (depends
    (rocq-autosubst-ocaml (>= 1.1+9.0))
    (coq-record-update (>= 0.3.6))
    (zarith (>= 1.14))
    (base (>= 0.15.1)))
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
