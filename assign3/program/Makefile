all: ngram.native karel.native
debug: ngram.byte karel.byte

BUILD = corebuild
FLAGS = -use-ocamlfind -use-menhir

%.byte: always
	$(BUILD) $(FLAGS) src/$@
	ln -sf _build/src/$@ $@

%.native: always
	$(BUILD) $(FLAGS) src/$@
	ln -sf _build/src/$@ $@

clean:
	rm -rf *.byte *.native *.top _build

always:

.PHONY: always
