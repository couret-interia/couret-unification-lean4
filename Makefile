.PHONY: build build-all clean validate \
        audit-imports audit-axioms audit-sorries audit-warnings \
        audit-axiom-declarations audit-true-statements audit-invariants \
        audit-collisions audit-orphans audit-reachability audit-scripts \
        audit-v38 audit-doctrine audit-all audit-historical \
        check-frozen gate-frozen \
        build-log-all tree report doctrine-check \
        snapshot test-all \
        python-moments python-gw python-tests python-defect \
        clean-reports

# ─── DIRECTORIES ───────────────────────────────────────────────────

REPORTS := build_reports

$(REPORTS):
	@mkdir -p $(REPORTS)

# ─── BUILDS ────────────────────────────────────────────────────────

build:
	lake build

build-all:
	lake build CouretUnification.All

clean:
	lake clean

clean-reports:
	rm -rf $(REPORTS)

# ─── ARCHITECTURE ──────────────────────────────────────────────────

tree: $(REPORTS)
	tree --gitignore 2>&1 | tee $(REPORTS)/ARCHITECTURE-tree.txt

# ─── BUILD ET LOG ──────────────────────────────────────────────────

build-log-all: $(REPORTS)
	lake build CouretUnification.All 2>&1 | tee $(REPORTS)/build.log
	grep -E "^error:|error:" $(REPORTS)/build.log | sort -u \
	    > $(REPORTS)/errors_unique.txt
	grep -E "^warning:|warning:" $(REPORTS)/build.log | sort -u \
	    > $(REPORTS)/warnings_unique.txt
	@echo "=== Résumé du build ==="
	@echo "Erreurs uniques  : $$(wc -l < $(REPORTS)/errors_unique.txt)"
	@echo "Warnings uniques : $$(wc -l < $(REPORTS)/warnings_unique.txt)"

# ─── AUDIT D'INTÉGRITÉ — INTERNE ──────────────────────────────────

audit-imports: $(REPORTS)
	@grep -rh '^import CouretUnification\.' lean/ \
	  | awk '{print $$2}' \
	  | sort -u \
	  | while IFS= read -r mod; do \
	      path=$$(printf '%s\n' "$$mod" | sed 's|\.|/|g; s|^|lean/|; s|$$|.lean|'); \
	      [ -f "$$path" ] || echo "BROKEN: $$mod (cherche a $$path)"; \
	    done | tee $(REPORTS)/broken_imports.txt

audit-axioms: $(REPORTS)
	lake build CouretUnification.Audit.PrintAxioms 2>&1 \
	    | tee $(REPORTS)/audit-axioms.log

audit-sorries: build-log-all
	grep "declaration uses \`sorry\`" $(REPORTS)/build.log \
	  | sed 's/^warning: //' \
	  | sort -u > $(REPORTS)/sorries_declarations.txt
	@echo "=== Sorries (déclarations) ==="
	@cat $(REPORTS)/sorries_declarations.txt
	@echo "=== Nombre déclarations : $$(wc -l < $(REPORTS)/sorries_declarations.txt) ==="

audit-warnings: build-log-all
	grep -E "^warning:" $(REPORTS)/build.log \
	  | grep -v "declaration uses \`sorry\`" \
	  | sort -u > $(REPORTS)/warnings_non_sorry.txt
	@echo "=== Warnings non-sorry ==="
	@cat $(REPORTS)/warnings_non_sorry.txt

audit-axiom-declarations: $(REPORTS)
	@echo "=== Déclarations 'axiom' dans le code (hors commentaires) ===" \
	    | tee $(REPORTS)/axiom_declarations.txt
	@grep -rn '^[[:space:]]*axiom[[:space:]]' lean/CouretUnification/ 2>/dev/null \
	    | tee -a $(REPORTS)/axiom_declarations.txt || echo "(aucun)" \
	    | tee -a $(REPORTS)/axiom_declarations.txt

audit-true-statements: $(REPORTS)
	@echo "=== Théorèmes ': True := ...' (exceptions d'anchor à auditer) ===" \
	    | tee $(REPORTS)/true_statements.txt
	@grep -rn ": True[[:space:]]*:=" lean/CouretUnification/ 2>/dev/null \
	    | tee -a $(REPORTS)/true_statements.txt || echo "(aucun)" \
	    | tee -a $(REPORTS)/true_statements.txt

audit-invariants: $(REPORTS)
	@echo "=== Invariants cardinaux (RHClaimed, etc. doivent être false) ===" \
	    | tee $(REPORTS)/invariants.txt
	@grep -rn "RHClaimed\|HilbertPolyaClaimed\|Det2IdentityClaimed" \
	    lean/CouretUnification/ \
	  | grep -E "(:=|= false|= False)" \
	  | tee -a $(REPORTS)/invariants.txt

# ─── AUDIT D'INTÉGRITÉ — SCRIPTS EXTERNES ─────────────────────────

audit-collisions: $(REPORTS)
	bash scripts/audit_structure_collisions.sh \
	    2>&1 | tee $(REPORTS)/collisions.log

check-frozen: $(REPORTS)
	bash scripts/check_frozen_invariants.sh \
	    2>&1 | tee $(REPORTS)/frozen_invariants.log

gate-frozen: $(REPORTS)
	bash scripts/gate_no_frozen_imports_residue.sh \
	    2>&1 | tee $(REPORTS)/gate_frozen.log

audit-orphans: $(REPORTS)
	bash scripts/audit_orphans.sh \
	    2>&1 | tee $(REPORTS)/audit_orphans.log

audit-reachability: $(REPORTS)
	bash scripts/audit_reachability.sh \
	    2>&1 | tee $(REPORTS)/audit_reachability.log

audit-doctrine: $(REPORTS)
	bash scripts/audit_v38_global_doctrine.sh \
	    2>&1 | tee $(REPORTS)/audit_v38_global_doctrine.log

audit-scripts: $(REPORTS)
	cd lean/ && bash ../scripts/sorry_audit.sh \
	    2>&1 | tee ../$(REPORTS)/sorry_audit_detailed.log

audit-v38: $(REPORTS)
	bash scripts/audit_v38_harmonisee.sh lean \
	    2>&1 | tee $(REPORTS)/audit_v38_harmonisee.log

# ─── ANCIENS AUDITS : V36 + V37 AGGRÉGÉS ──────────────────────────

audit-v37: $(REPORTS)
	bash scripts/audit_v37_aggregation.sh \
	    2>&1 | tee $(REPORTS)/audit_v37.log

# ─── MÉTA-CIBLE : LANCE TOUS LES AUDITS ───────────────────────────

audit-all: build-log-all audit-imports audit-axioms audit-sorries \
           audit-warnings audit-axiom-declarations audit-true-statements \
           audit-invariants audit-collisions check-frozen gate-frozen \
           audit-orphans audit-reachability audit-v38 audit-doctrine audit-scripts
	@echo ""
	@echo "═══════════════════════════════════════════════════"
	@echo " AUDIT COMPLET — $$(date +%Y-%m-%d) — $$(date +%H:%M)"
	@echo "═══════════════════════════════════════════════════"
	@echo "Tous les rapports sont dans $(REPORTS)/"
	@ls -1 $(REPORTS)/

# ─── VALIDATION (existant) ────────────────────────────────────────

validate:
	bash scripts/validate_pack.sh

test-all:
	cd scripts && bash run_all_tests.sh

# ─── SCRIPTS PYTHON ───────────────────────────────────────────────

python-moments: $(REPORTS)
	python3 scripts/compute_moments.py \
	    2>&1 | tee $(REPORTS)/python_moments.log

python-gw: $(REPORTS)
	python3 python/guinand_weil_channelwise.py \
	    2>&1 | tee $(REPORTS)/python_gw.log

python-tests: $(REPORTS)
	python3 python/couret_full_tests.py \
	    2>&1 | tee $(REPORTS)/python_tests.log

python-defect: $(REPORTS)
	python3 python/couret_defect_lab.py \
	    2>&1 | tee $(REPORTS)/python_defect.log

# ─── REPORTING ────────────────────────────────────────────────────

# Rapport consolidé v38.x — utile avant chaque livraison majeure
report: tree audit-all
	@echo ""
	@echo "═══════════════════════════════════════════════════"
	@echo " RAPPORT DOCTRINAL v38.x — $$(date +%Y-%m-%d)"
	@echo "═══════════════════════════════════════════════════"
	@echo ""
	@echo "Build All :"
	@grep -E "Build completed|jobs\)" $(REPORTS)/build.log | tail -1
	@echo ""
	@echo "Sorries (déclarations) : $$(wc -l < $(REPORTS)/sorries_declarations.txt)"
	@echo "Warnings non-sorry     : $$(wc -l < $(REPORTS)/warnings_non_sorry.txt)"
	@echo "Imports cassés         : $$(wc -l < $(REPORTS)/broken_imports.txt)"
	@echo "Axiomes déclarés       : $$(grep -rn '^[[:space:]]*axiom[[:space:]]' lean/ 2>/dev/null | wc -l)"
	@echo "Théorèmes ': True := …': $$(grep -rn ': True[[:space:]]*:=' lean/ 2>/dev/null | wc -l)"
	@echo ""

# ─── SNAPSHOT (pour livraisons majeures) ──────────────────────────

# Crée un snapshot daté du build et des audits
snapshot: report
	@mkdir -p $(REPORTS)/snapshots/$$(date +%Y-%m-%d)
	@cp $(REPORTS)/*.log $(REPORTS)/*.txt \
	    $(REPORTS)/snapshots/$$(date +%Y-%m-%d)/ 2>/dev/null || true
	@echo "Snapshot enregistré dans $(REPORTS)/snapshots/$$(date +%Y-%m-%d)/"

# ─── DOCTRINE CHECK RAPIDE ────────────────────────────────────────

doctrine-check: audit-axiom-declarations audit-true-statements \
                audit-invariants check-frozen
	@echo ""
	@echo "Doctrine check terminé."
	@echo "Voir $(REPORTS)/ pour les détails."
