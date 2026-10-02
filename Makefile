.PHONY: all build test check fmt

# Lake targets share build artifacts; keep project checks sequential.
.NOTPARALLEL:

all: build test check

build:
	time lake build

b: build

test:
	time lake build Tests

t: test

check:
	time lake lint
	time ./scripts/fmt-changed.sh --allow-dirty --check

c: check

fmt:
	time ./scripts/fmt-changed.sh --allow-dirty
	time lake build
	time lake lint

f: fmt
