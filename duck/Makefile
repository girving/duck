GHC = ghc
GHCFLAGS = -O -Wall -Werror -fwarn-tabs -fno-warn-missing-signatures -fno-warn-name-shadowing
HAPPY = happy
HAPPYFLAGS = -agc
ALEX = alex
ALEXFLAGS = -g

all: duck

info: Parse.info

.PHONY: duck
duck: Duck.hs others
	$(GHC) $(GHCFLAGS) --make $< -o $@

others: Parse.hs Lex.hs

%.hs: %.y
	$(HAPPY) $(HAPPYFLAGS) $< -o $@

%.info: %.y
	$(HAPPY) $(HAPPYFLAGS) $< -i$@

%.hs: %.x
	$(ALEX) $(ALEXFLAGS) $< -o $@

.PHONY: clean
clean:
	rm -f *.o *.hi *.info duck Parse.hs 
