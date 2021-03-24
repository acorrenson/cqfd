
src/kernel.ml: theories/*.why
	why3 extract --modular --recursive-deps -D ocaml64 -L ./theories -o src/ strategies.Strategies

.PHONY: prove
prove: ./theories/*.why
	why3 prove -P Alt-Ergo -L ./theories $^

clean:
	rm -rf src/*.bak


