SHELL := /bin/bash

AGDA_DATADIR ?= _build
AUTOGEN_DIR ?= trees/stt/autogen
HTML_DIR ?= output/agda-synthetic-categories/html
EVERYTHING_FILE ?= src/Everything.agda
WATCH_DIR ?= src
PORT ?= 1313
DUP_DIR ?= ./trees/
AGDA_FLAGS ?= --without-K --rewriting --guardedness --flat-split --level-universe --postfix-projections --local-confluence-check --no-qualified-instances -WnoWithoutKFlagPrimEraseEquality
EVERYTHING_INPUTS := $(shell find src -type f \( -name '*.agda' -o -name '*.lagda.tree' \) ! -name 'Everything.agda' | sort)

.PHONY: help generate-everything prepare-agda-datadir sync-forest-src typecheck build-forest watch-agda check-port watch-forest server check-dup clean-agda clean-forester clean serve

help:
	@echo "Available targets:"
	@echo "  make build-forest               # Generate Everything.agda + Agda/Forester trees/html"
	@echo "  make sync-forest-src            # Copy source .lagda.tree files into trees/stt/autogen without highlighting and links"
	@echo "  make typecheck                  # Generate Everything.agda and typecheck with agda"
	@echo "  make watch-agda                 # Rebuild Agda output when src/ changes"
	@echo "  make watch-forest [PORT=<port>] # Run forester watch server (default: 1313)"
	@echo "  make server [PORT=<port>]       # Run watch-agda + watch-forest together (default: 1313)"
	@echo "  make serve [PORT=<port>]        # Serve ./result with python http.server (default: 1313)"
	@echo "  make check-dup                  # Find duplicate subtree references (DIR=... optional)"
	@echo "  make clean-agda                 # Remove generated agda artifacts"
	@echo "  make clean-forester             # Remove generated forester artifacts"
	@echo "  make clean                      # Remove all generated build artifacts"

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
	time Agda_datadir="./$(AGDA_DATADIR)" agda $(AGDA_FLAGS) -i src "$(EVERYTHING_FILE)" -j

sync-forest-src:
	@mkdir -p "$(AUTOGEN_DIR)"
	@find ./src -name '*.lagda.tree' | while read -r file; do \
		rel=$${file#./src/}; \
		newname=$${rel//\//.}; \
		newname=$${newname/.lagda/}; \
		dest="$(AUTOGEN_DIR)/$$newname"; \
		cp "$$file" "$$dest"; \
	done

build-forest: $(EVERYTHING_FILE) prepare-agda-datadir
	@mkdir -p "$(AGDA_DATADIR)" "$(AGDA_DATADIR)/lib" "$(AUTOGEN_DIR)" "$(HTML_DIR)"
	@Agda_datadir="./$(AGDA_DATADIR)" agda-forester --forest -o"$(AUTOGEN_DIR)" --fhtml-dir="$(HTML_DIR)" --fhtml-link-root="/agda-synthetic-categories/html/" --fhtml-css-path="../Agda.css" --fforest-root="/agda-synthetic-categories/" "$(EVERYTHING_FILE)" -j

watch-agda:
	@$(MAKE) --no-print-directory build-forest
	@fswatch -o "$(WATCH_DIR)" | while read -r _; do \
		echo "Rebuilding forest"; \
		time $(MAKE) --no-print-directory build-forest; \
		echo "Done"; \
		echo; \
	done

check-port:
	@if ! [[ "$(PORT)" =~ ^[0-9]+$$ ]] || [ "$(PORT)" -lt 1 ] || [ "$(PORT)" -gt 65535 ]; then \
		echo "Error: PORT must be an integer in the range 1-65535 (got: $(PORT))." >&2; \
		exit 1; \
	fi
	@if lsof -nP -iTCP:"$(PORT)" -sTCP:LISTEN >/dev/null 2>&1; then \
		echo "Error: port $(PORT) is already in use." >&2; \
		echo "Stop the existing process or rerun with PORT=<port>." >&2; \
		lsof -nP -iTCP:"$(PORT)" -sTCP:LISTEN >&2 || true; \
		exit 1; \
	fi

watch-forest: check-port
	@echo "Serving forest on http://localhost:$(PORT)"
	@forest watch "$(PORT)" -- "build --dev"

server:
	@$(MAKE) --no-print-directory check-port
	@trap 'kill 0' EXIT; \
	$(MAKE) --no-print-directory watch-agda & \
	$(MAKE) --no-print-directory watch-forest; \
	wait

check-dup:
	@DIR="$(DUP_DIR)"; \
	{ \
		rg -n --no-heading --no-ignore-vcs -o --glob '*.tree' 'subtree\[[0-9A-Za-z\-]*\]' "$$DIR"; \
		find "$$DIR" -name '*.tree'; \
	} | awk '\
	/subtree\[/ { \
		split($$0, a, ":"); \
		id = a[3]; \
		sub(/^subtree\[/, "", id); \
		sub(/\]$$/, "", id); \
		loc = a[1] ":" a[2]; \
	} \
	/\.tree$$/ { \
		loc = $$0; \
		id = $$0; \
		sub(/^.*\//, "", id); \
		sub(/\.tree$$/, "", id); \
	} \
	{ \
		count[id]++; \
		occ[id] = occ[id] "\n  " loc; \
	} \
	END { \
		err = 0; \
		for (id in count) \
			if (count[id] > 1) { \
				err = 1; \
				printf "DUPLICATE %s (%d occurrences):\n%s\n\n", id, count[id], occ[id]; \
		        } \
		exit err ; \
	}'

check-forest-no-typecheck: sync-forest-src
	@mkdir -p "$(HTML_DIR)"
	@$(MAKE) --no-print-directory check-dup
	@forester build

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
	@python3 -m http.server "$(PORT)" -d result
