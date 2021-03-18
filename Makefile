
src/proof.ml: theories/proof.why
	why3 extract -D ocaml64 -L ./theories --recursive-deps $< -o $@

.PHONY: prove
prove: ./theories/*.why
	why3 prove -P Alt-Ergo -L ./theories $^


