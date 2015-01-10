all: typecheck doc
.PHONY: all typecheck doc clean clobber

typecheck: Main.hs
	runhaskell -W -Wall Main.hs

doc:
	haddock --html -o doc Main.hs

clean:
clobber: clean
	rm -rf doc
