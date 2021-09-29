all: build

build:
	mdbook build

test: build
	cargo run

serve:
	mdbook serve

serve_open:
	mdbook serve --open

get_deps:
	cargo install mdbook mdbook-linkcheck

update_deps:
	cargo install --force mdbook mdbook-linkcheck
