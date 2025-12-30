TEMPLATES := $(wildcard templates/*.html)

site: render.py $(TEMPLATES)
	mkdir -p _site
	python render.py

serve: site
	cd _site && python -m http.server

clean:
	rm -rf _site

.PHONY: site serve clean
