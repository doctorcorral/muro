AGDA  := agda
# --no-libraries: vendored stdlib ships extra .agda-lib files (tests, cubical).
AFLAGS := --no-libraries -i agda -i vendor/agda-stdlib/src --warning=noUnsupportedIndexedMatch

.PHONY: agda agda-syntax agda-check elixir clean

agda-syntax:
	$(AGDA) $(AFLAGS) agda/Muro/Syntax.agda
	$(AGDA) $(AFLAGS) agda/Muro/Subst.agda

agda-check:
	$(AGDA) $(AFLAGS) agda/Muro/Check.agda

agda:
	$(AGDA) $(AFLAGS) agda/Muro.agda

elixir:
	mix test

clean:
	find agda -name '*.agdai' -delete
	rm -rf agda/_build _build deps
