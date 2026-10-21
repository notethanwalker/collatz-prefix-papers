.PHONY: all check clean
all: papers/entropy-height.pdf papers/bounded-deviations.pdf
papers/%.pdf: papers/%.tex
	mkdir -p build
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build $<
	pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build $<
	cp build/$*.pdf $@
check:
	python3 checks/check.py
clean:
	rm -rf build
