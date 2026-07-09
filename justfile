build:
  dune build

test:
  dune test

cli *args:
  @dune exec bin/main.exe -- {{args}}

clean:
  dune clean
