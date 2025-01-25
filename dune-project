(lang dune 3.17)
(using coq 0.10)

(name iris-rwasm)
(version 0.1)

(generate_opam_files true)
(license MIT)
(source (github hackedy/iris-rwasm))

(package
  (name iris-rwasm)
  (synopsis "RichWasm formalization in Coq and Iris")
  (description "RichWasm formalization in Coq based on Iris-Wasm.")
  (depends
    (iris-wasm (>= 2.0)))
  (maintainers
    Ryan Doenges
    Brianna Marshall)
  (authors
    Ryan Doenges
    Brianna Marshall
    Maxime Legoupil
    Amal Ahmed))
