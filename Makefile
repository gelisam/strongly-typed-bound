all: typecheck doc
.PHONY: all typecheck doc clean clobber

typecheck: StronglyTypedBound.hs
	runhaskell -W -Wall StronglyTypedBound.hs

doc:
	haddock --html -o doc StronglyTypedBound.hs

clean:
clobber: clean
	rm -rf doc
