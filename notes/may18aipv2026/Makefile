# Build LaTeX scaffolds in this directory (slides + poster).
# Usage:
#   make            — build all PDFs
#   make slides     — build aipv2026_slides.pdf only
#   make poster     — build aipv2026_poster.pdf only
#   make clean      — remove auxiliary files
#   make distclean  — clean + remove PDFs

TEXDIR := $(abspath .)
PDFLATEX := pdflatex
LATEXFLAGS := -interaction=nonstopmode -file-line-error -halt-on-error

SLIDES_TEX := aipv2026_slides.tex
POSTER_TEX := aipv2026_poster.tex
SLIDES_PDF := $(SLIDES_TEX:.tex=.pdf)
POSTER_PDF := $(POSTER_TEX:.tex=.pdf)

PDFS := $(SLIDES_PDF) $(POSTER_PDF)

.PHONY: all slides poster clean distclean

all: $(PDFS)

slides: $(SLIDES_PDF)

poster: $(POSTER_PDF)

$(SLIDES_PDF): $(SLIDES_TEX)
	cd "$(TEXDIR)" && $(PDFLATEX) $(LATEXFLAGS) "$(SLIDES_TEX)"
	cd "$(TEXDIR)" && $(PDFLATEX) $(LATEXFLAGS) "$(SLIDES_TEX)"

$(POSTER_PDF): $(POSTER_TEX)
	cd "$(TEXDIR)" && $(PDFLATEX) $(LATEXFLAGS) "$(POSTER_TEX)"
	cd "$(TEXDIR)" && $(PDFLATEX) $(LATEXFLAGS) "$(POSTER_TEX)"

clean:
	cd "$(TEXDIR)" && rm -f \
	  *.aux *.log *.out *.nav *.snm *.toc *.vrb *.bbl *.blg *.fdb_latexmk *.fls *.synctex.gz

distclean: clean
	cd "$(TEXDIR)" && rm -f $(PDFS)
