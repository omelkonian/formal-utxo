default: site

site:
	agda --html --html-dir=docs Main.agda && cp docs/Main.html docs/index.html

clean:
	rm -rf docs/

# Travis Setup (install Agda, the Agda standard library, acknowledgements, etc.)
travis-setup:\
	$(HOME)/.local/bin/agda\
	$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/src\
	$(HOME)/my-agda-prelude-master/Everything.agda\
	$(HOME)/.agda/libraries

.phony: travis-setup

$(HOME)/.local/bin/agda:
	curl -L https://github.com/agda/agda/archive/v$(AGDA_VERSION).zip -o $(HOME)/agda-$(AGDA_VERSION).zip
	unzip -qq $(HOME)/agda-$(AGDA_VERSION).zip -d $(HOME)
	cd $(HOME)/agda-$(AGDA_VERSION);\
		stack install --stack-yaml=stack-8.0.2.yaml

$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/src:
	curl -L https://github.com/agda/agda-stdlib/archive/v$(AGDA_STDLIB_VERSION).zip -o $(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION).zip
	unzip -qq $(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION).zip -d $(HOME)

$(HOME)/my-agda-prelude-master/Everything.agda:
	curl -L https://github.com/omelkonian/my-agda-prelude/archive/master.zip -o $(HOME)/my-agda-prelude-master.zip
	unzip -qq $(HOME)/my-agda-prelude-master.zip -d $(HOME)

$(HOME)/.agda/libraries:
	mkdir -p $(HOME)/.agda
	echo "$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/standard-library.agda-lib" >> $(HOME)/.agda/libraries
	echo "$(HOME)/my-agda-prelude-master/my-agda-prelude.agda-lib"              >> $(HOME)/.agda/libraries
