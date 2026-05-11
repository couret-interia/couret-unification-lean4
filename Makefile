.PHONY: build clean validate

build:
	lake build

clean:
	lake clean

validate:
	bash scripts/validate_pack.sh

# Tous les imports CouretUnification.* qui ne pointent plus sur un fichier vivant
audit-imports:
	@grep -rh '^import CouretUnification\.' lean/ \
	  | sort -u \
	  | sed 's/^import //' \
	  | while IFS= read -r mod; do \
	      path=$$(printf '%s\n' "$$mod" | sed 's|\.|/|g; s|^|lean/|; s|$$|.lean|'); \
	      [ -f "$$path" ] || echo "BROKEN: $$mod (cherche a $$path)"; \
	    done

build-log-all:
	lake build CouretUnification.All 2>&1 | tee build.log
	grep -E "^error:|error:" build.log | sort -u > errors_unique.txt
	grep -E "^warning:|warning:" build.log | sort -u > warnings_unique.txt

tree:
	tree --gitignore 2>&1 | tee ARCHITECTURE-tree.log
