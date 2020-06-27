default: site

site:
	agda --html --html-dir=docs --css=css/Agda.css Main.agda \
	  && cp docs/Main.html docs/index.html 

clean:
	rm -f docs/*.html

# Travis Setup (install Agda, the Agda standard library, acknowledgements, etc.)
travis-setup:\
	$(HOME)/.local/bin/agda\
	$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/src\
	$(HOME)/formal-prelude-master/Prelude/Main.agda\
	$(HOME)/.agda/libraries

.phony: travis-setup

$(HOME)/.local/bin/agda:
	curl -L https://github.com/agda/agda/archive/v$(AGDA_VERSION).zip -o $(HOME)/agda-$(AGDA_VERSION).zip
	unzip -qq $(HOME)/agda-$(AGDA_VERSION).zip -d $(HOME)
	cd $(HOME)/agda-$(AGDA_VERSION);\
		stack install --stack-yaml=stack-8.6.5.yaml

$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/src:
	curl -L https://github.com/agda/agda-stdlib/archive/v$(AGDA_STDLIB_VERSION).zip -o $(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION).zip
	unzip -qq $(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION).zip -d $(HOME)

$(HOME)/formal-prelude-master/Prelude/Main.agda:
	curl -L https://github.com/omelkonian/formal-prelude/archive/master.zip -o $(HOME)/formal-prelude-master.zip
	unzip -qq $(HOME)/formal-prelude-master.zip -d $(HOME)

$(HOME)/.agda/libraries:
	mkdir -p $(HOME)/.agda
	echo "$(HOME)/agda-stdlib-$(AGDA_STDLIB_VERSION)/standard-library.agda-lib" >> $(HOME)/.agda/libraries
	echo "$(HOME)/formal-prelude-master/formal-prelude.agda-lib"                >> $(HOME)/.agda/libraries
