all: main.native
debug: main.byte
test: always
	$(BUILD) $(FLAGS) -I src tests/interpreter_tests.native
	./interpreter_tests.native

BUILD = corebuild
# Force Apple's clang: Homebrew's llvm clang cannot link -lpthread on this SDK.
export OCAMLPARAM = cc=/usr/bin/clang,_
FLAGS = -use-ocamlfind -use-menhir

%.byte: always
	$(BUILD) $(FLAGS) src/$@

%.native: always
	$(BUILD) $(FLAGS) src/$@

clean:
	rm -rf main.byte main.native *.top _build

always:

.PHONY: always test
