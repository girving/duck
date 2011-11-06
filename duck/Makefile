TOPDIR=..
SETUP=cd $(TOPDIR) ; $(if $(wildcard $(TOPDIR)/Setup),./Setup,runhaskell ./Setup.hs)
CONFIG_DONE=$(TOPDIR)/dist/setup-config
CONFIGFLAGS=-O --enable-executable-profiling --enable-executable-dynamic --ghc-options=-Werror
DUCK=$(TOPDIR)/dist/build/duck/duck

TESTS = basic layout curry delay match io tyfun success types base-test expseq fac
TESTS_C = apply base ops null
TESTS_FAIL := $(patsubst test/fail/%.duck, fail/%, $(wildcard test/fail/*.duck))
TESTS_FAIL_R := $(patsubst test/fail-r/%.duck, fail-r/%, $(wildcard test/fail-r/*.duck))

default: duck

info: Parse.info

### Compile

.PHONY: $(DUCK)
$(DUCK): $(CONFIG_DONE)
	@echo "make: Entering directory \`..'"
	$(SETUP) build
	@echo "make: Leaving directory \`..'"

$(CONFIG_DONE): $(TOPDIR)/duck.cabal
	$(SETUP) configure $(CONFIGFLAGS)

duck: $(DUCK)
	ln -sf $< $@

# cabal doesn't have an easy way of generating these
%.info: %.y
	happy -agc $< -i$@
	rm -f $*.hs

### Generate Haskell files from Duck

GEN = ./duck --haskell
.PHONY: gen
gen:
	$(GEN) var.duck > Gen/Var.hs
	$(GEN) type.duck > Gen/Type.hs
	$(GEN) preType.duck > Gen/PreType.hs
	$(GEN) srcLoc.duck > Gen/SrcLoc.hs
	$(GEN) prims.duck > Gen/Prims.hs
	$(GEN) lir.duck > Gen/Lir.hs
	$(GEN) value.duck > Gen/Value.hs
	$(GEN) interp.duck > Gen/Interp.hs

### Test

ALL_TESTS = $(TESTS) $(TESTS_C) $(TESTS_FAIL) $(TESTS_FAIL_R)
.PHONY: test $(ALL_TESTS)
test: $(ALL_TESTS)
	@echo
	@echo All tests passed!
$(TESTS): duck
	./duck test/$@.duck
$(TESTS_C): duck
	./duck -c test/$@.duck
$(TESTS_FAIL): duck
	@echo "! ./duck -Itest test/$@.duck"
	@./duck -Itest test/$@.duck; s=$$?; if [ $$s -eq 1 ]; then :; else echo $@ failed: exit status $$s != 1; false; fi
$(TESTS_FAIL_R): duck
	@echo "! ./duck -Itest test/$@.duck"
	@./duck -Itest test/$@.duck; s=$$?; if [ $$s -eq 3 ]; then :; else echo $@ failed: exit status $$s != 3; false; fi

### Misc

tags: $(wildcard *.hs) Parse.y Lex.x
	hasktags -c $^

.PHONY: clean
clean:
	$(SETUP) clean -s
