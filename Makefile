all: build check

build:
	time lake build

check:
	time lake lint
	time ./scripts/fmt-changed.sh --check

fmt:
	time ./scripts/fmt-changed.sh
	time lake build
	time lake lint
