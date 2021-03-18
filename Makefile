
src/proof.ml: theories/proof.why
	why3 extract -D ocaml64 -L ./theories --recursive-deps $< -o $@