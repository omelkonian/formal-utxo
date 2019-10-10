default: site

site:
	agda --html --html-dir=docs Main.agda && cp docs/Main.html docs/index.html

clean:
	rm -rf docs/
