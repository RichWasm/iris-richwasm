(lang dune 3.16)
(using coq 0.9)

(name iris-rwasm)
(version 0.1)

(generate_opam_files true)
(source (github hackedy/iris-rwasm))

(package
  (name iris-rwasm)
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
