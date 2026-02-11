SHELL := /bin/bash

AGDA_DATADIR ?= _build
AUTOGEN_DIR ?= trees/stt/autogen
HTML_DIR ?= output/html
EVERYTHING_FILE ?= src/Everything.agda
WATCH_DIR ?= src
FOREST_PORT ?= 1313
DUP_DIR ?= .
AGDA_FLAGS ?= --without-K --rewriting --guardedness --flat-split --postfix-projections --local-confluence-check --no-qualified-instances -WnoWithoutKFlagPrimEraseEquality
EVERYTHING_INPUTS := $(shell find src -type f \( -name '*.agda' -o -name '*.lagda.tree' \) ! -name 'Everything.agda' | sort)

.PHONY: help generate-everything prepare-agda-datadir typecheck build-forest watch-agda check-port watch-forest server check-dup clean-agda clean-forester clean

help:
	@echo "Available targets:"
	@echo "  make build-forest      # Generate Everything.agda + Agda/Forester trees/html"
	@echo "  make typecheck         # Generate Everything.agda and typecheck with agda"
	@echo "  make watch-agda        # Rebuild Agda output when src/ changes"
	@echo "  make watch-forest      # Run forester watch server"
	@echo "  make server            # Run watch-agda + watch-forest together"
	@echo "  make check-dup         # Find duplicate subtree references (DIR=... optional)"
	@echo "  make clean-agda        # Remove generated agda artifacts"
	@echo "  make clean-forester    # Remove generated forester artifacts"
	@echo "  make clean             # Remove generated build artifacts"

$(EVERYTHING_FILE): scripts/generateEverything.sh $(EVERYTHING_INPUTS)
	@bash ./scripts/generateEverything.sh

generate-everything: $(EVERYTHING_FILE)

prepare-agda-datadir:
	@mkdir -p "$(AGDA_DATADIR)/lib"
	@if [ ! -f "$(AGDA_DATADIR)/lib/prim/Agda/Primitive.agda" ]; then \
		agda_data_dir="$$(agda --print-agda-data-dir)"; \
		echo "Seeding $(AGDA_DATADIR)/lib/prim from $$agda_data_dir/lib/prim"; \
		rm -rf "$(AGDA_DATADIR)/lib/prim"; \
		cp -R "$$agda_data_dir/lib/prim" "$(AGDA_DATADIR)/lib/"; \
	fi
	@chmod -R u+w "$(AGDA_DATADIR)/lib/prim" || true
	@mkdir -p "$(AGDA_DATADIR)/lib/prim/_build"

typecheck: $(EVERYTHING_FILE) prepare-agda-datadir
	@mkdir -p "$(AGDA_DATADIR)" "$(AGDA_DATADIR)/lib"
	@TIMEFORMAT='Typecheck elapsed: %3lR'; \
	time Agda_datadir="./$(AGDA_DATADIR)" agda $(AGDA_FLAGS) -i src "$(EVERYTHING_FILE)"

build-forest: $(EVERYTHING_FILE) prepare-agda-datadir
	@mkdir -p "$(AGDA_DATADIR)" "$(AGDA_DATADIR)/lib" "$(AUTOGEN_DIR)" "$(HTML_DIR)"
	@Agda_datadir="./$(AGDA_DATADIR)" agda-forester --forest -o"$(AUTOGEN_DIR)" --fhtml-dir="$(HTML_DIR)" "$(EVERYTHING_FILE)"

watch-agda:
	@$(MAKE) --no-print-directory build-forest
	@fswatch -o "$(WATCH_DIR)" | while read -r _; do \
		echo "Rebuilding forest"; \
		time $(MAKE) --no-print-directory build-forest; \
		echo "Done"; \
		echo; \
	done

check-port:
	@if lsof -nP -iTCP:"$(FOREST_PORT)" -sTCP:LISTEN >/dev/null 2>&1; then \
		echo "Error: port $(FOREST_PORT) is already in use." >&2; \
		echo "Stop the existing process or rerun with FOREST_PORT=<port>." >&2; \
		lsof -nP -iTCP:"$(FOREST_PORT)" -sTCP:LISTEN >&2 || true; \
		exit 1; \
	fi

watch-forest: check-port
	@echo "Serving forest on http://localhost:$(FOREST_PORT)"
	@forest watch "$(FOREST_PORT)" -- "build --dev"

server:
	@$(MAKE) --no-print-directory check-port
	@trap 'kill 0' EXIT; \
	$(MAKE) --no-print-directory watch-agda & \
	$(MAKE) --no-print-directory watch-forest; \
	wait

check-dup:
	@DIR="$(DUP_DIR)"; \
	rg -n --no-heading -o --glob '*.lagda.tree' 'subtree\[stt-[0-9A-Z]{4}\]' "$$DIR" \
	| awk -F: '\
		{ \
			id = $$3; \
			sub(/^subtree\[/, "", id); \
			sub(/\]$$/, "", id); \
			occurrences[id] = occurrences[id] "\n  " $$1 ":" $$2; \
			counts[id]++; \
		} \
		END { \
			for (id in counts) { \
				if (counts[id] > 1) { \
					printf "DUPLICATE %s (%d occurrences):\n%s\n\n", id, counts[id], occurrences[id]; \
				} \
			} \
		}'

clean-agda:
	@chmod -R u+w _build 2>/dev/null || true
	@rm -rf _build
	@rm -f src/Everything.agda
	@find . -type f \( -name '*.agdai' -o -name '*.agdai~' \) -delete
	@find . -type d \( -name MAlonzo \) -prune -exec rm -rf {} +

clean-forester:
	@chmod -R u+w _build 2>/dev/null || true
	@rm -rf _tmp build output results assets/html
	@rm -f forest-map.json
	@find . -type d \( -name autogen \) -prune -exec rm -rf {} +

clean: clean-agda clean-forester
serve:
	@python3 -m http.server "$(FOREST_PORT)" -d result
