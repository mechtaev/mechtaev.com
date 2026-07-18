TEMPLATES := $(wildcard templates/*.html)

site: cv render.py $(TEMPLATES)
	mkdir -p _site
	uv run python render.py

cv: cv/generate_cv.py cv/cv_template.tex.j2 data.json
	uv run cv/generate_cv.py

serve: site
	cd _site && uv run python -m http.server

clean:
	rm -rf _site cv/sergey_mechtaev_cv.tex cv/sergey_mechtaev_cv.pdf

.PHONY: site serve clean cv
