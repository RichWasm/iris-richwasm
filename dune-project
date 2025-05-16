(lang dune 3.18)
(using coq 0.9)

(name iris-richwasm)
(version 0.1)

(generate_opam_files true)
(source (github RichWasm/iris-richwasm))

(package
  (name iris-richwasm)
  (synopsis "RichWasm formalization in Coq and Iris")
  (description "RichWasm formalization in Coq based on Iris-Wasm.")
  (maintainers
    "Ryan Doenges"
    "Brianna Marshall")
  (authors
    "Ryan Doenges"
    "Brianna Marshall"
    "Maxime Legoupil"
    "Amal Ahmed")
  (depends
    (dune (>= 3.18))
    (coq (>= 8.20.1))
    (coq-iris (>= 4.3.0))
    (coq-stdpp (>= 1.11.0)) 
    (coq-compcert (>= 3.15))
    (coq-ext-lib (>= 0.13.0))
    (coq-mathcomp-ssreflect (>= 2.3.0))
    (coq-parseque (>= 0.2.1))
    (coq-itree (>= 5.2.0))
    (iris-wasm (= dev)) ; this is a pin-depend, see .opam.template file
    (cmdliner (>= 1.3.0))
    (linenoise (>= 1.5.1))
    (mdx (>= 2.5.0))))
