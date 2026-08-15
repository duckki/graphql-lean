
all: build check

build:
	time lake build

FMT_TARGETS := $(shell git diff --name-only --diff-filter=ACMR origin/main... -- '*.lean' | while IFS= read -r f; do test -e "$$f" && printf '%s\n' "$$f"; done)

check:
	time lake lint
	time lake exe fmt --check $(FMT_TARGETS)

fmt:
	time lake exe fmt $(FMT_TARGETS)
	time lake build
	time lake lint
