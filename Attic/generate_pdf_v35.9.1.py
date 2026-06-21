#!/usr/bin/env python3
"""
Couret-Unification — Dossier Intégrations complètes v35.9.1
Compagnon du PDF Horizons. Consolide les 10 fichiers uploadés
le 24 avril 2026 (Rapport impasses, note architecture Thomas,
TimeBridge LTB-0, ModThirtyChecker FCI, 3 candidats algèbre arithmétique).

Pour Bernard Couret (1928-1999, Istres).
"""

from reportlab.lib.pagesizes import A4
from reportlab.lib import colors
from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
from reportlab.lib.units import cm, mm
from reportlab.lib.enums import TA_LEFT, TA_CENTER, TA_JUSTIFY
from reportlab.platypus import (
    SimpleDocTemplate, Paragraph, Spacer, PageBreak, Table, TableStyle,
    HRFlowable,
)

NAVY = colors.HexColor("#0B1F3A")
GOLD = colors.HexColor("#B8860B")
DIAMOND = colors.HexColor("#4A90A4")
PLATINUM = colors.HexColor("#5C6B73")
INK = colors.HexColor("#1a1a1a")
MUTED = colors.HexColor("#666666")
LIGHT = colors.HexColor("#f4f4f4")
RED = colors.HexColor("#C0392B")
GREEN = colors.HexColor("#2C7A3E")
VIOLET = colors.HexColor("#5B2C6F")
ORANGE = colors.HexColor("#D35400")

styles = getSampleStyleSheet()

def mk(name, parent, **kw):
    return ParagraphStyle(name, parent=parent, **kw)

TITLE_BIG = mk("TB", styles["Title"], fontSize=24, leading=30, textColor=NAVY,
    alignment=TA_CENTER, spaceAfter=12, fontName="Helvetica-Bold")
TITLE_SUB = mk("TS", styles["Title"], fontSize=14, leading=19, textColor=PLATINUM,
    alignment=TA_CENTER, spaceAfter=10, fontName="Helvetica")
H1 = mk("H1", styles["Heading1"], fontSize=17, leading=22, textColor=NAVY,
    spaceBefore=16, spaceAfter=9, fontName="Helvetica-Bold", keepWithNext=1)
H2 = mk("H2", styles["Heading2"], fontSize=13, leading=17, textColor=DIAMOND,
    spaceBefore=12, spaceAfter=6, fontName="Helvetica-Bold", keepWithNext=1)
H3 = mk("H3", styles["Heading3"], fontSize=11.5, leading=14, textColor=PLATINUM,
    spaceBefore=9, spaceAfter=4, fontName="Helvetica-Bold", keepWithNext=1)
BODY = mk("Body", styles["BodyText"], fontSize=10, leading=14, textColor=INK,
    alignment=TA_JUSTIFY, spaceAfter=5, fontName="Helvetica")
CODE = mk("Code", BODY, fontName="Courier", fontSize=8.3, leading=10.5,
    textColor=INK, leftIndent=10, rightIndent=10,
    spaceBefore=3, spaceAfter=3, alignment=TA_LEFT,
    backColor=LIGHT, borderPadding=5)
DEDICACE = mk("Ded", BODY, alignment=TA_CENTER, fontName="Helvetica-Oblique",
    textColor=MUTED, fontSize=10, leading=14)
INVARIANT = mk("Inv", BODY, alignment=TA_CENTER, fontName="Courier-Bold",
    fontSize=10.5, leading=13, textColor=RED)

def P(t, s=BODY): return Paragraph(t, s)
def SP(h=5): return Spacer(1, h)
def bar(): return HRFlowable(width="100%", thickness=1.2, color=GOLD,
                             spaceBefore=2, spaceAfter=9)
def bullet(t, s=BODY): return Paragraph(f"• {t}", s)
def code(txt):
    return [P(l.replace(" ", "&nbsp;"), CODE) for l in txt.strip().split("\n")]

def tbl(data, cw, header=True, font=8.5, align=None, colors_row=None):
    t = Table(data, colWidths=cw, repeatRows=1 if header else 0)
    s = [
        ("FONT", (0,0), (-1,-1), "Helvetica", font),
        ("ALIGN", (0,0), (-1,-1), "LEFT"),
        ("VALIGN", (0,0), (-1,-1), "TOP"),
        ("GRID", (0,0), (-1,-1), 0.3, MUTED),
        ("LEFTPADDING", (0,0), (-1,-1), 4),
        ("RIGHTPADDING", (0,0), (-1,-1), 4),
        ("TOPPADDING", (0,0), (-1,-1), 3),
        ("BOTTOMPADDING", (0,0), (-1,-1), 3),
    ]
    if header:
        s += [("FONT", (0,0), (-1,0), "Helvetica-Bold", font),
              ("BACKGROUND", (0,0), (-1,0), NAVY),
              ("TEXTCOLOR", (0,0), (-1,0), colors.white)]
    if align:
        for c, a in align.items():
            s.append(("ALIGN", (c, 1 if header else 0), (c, -1), a))
    if colors_row:
        for row_idx, col in colors_row.items():
            s.append(("BACKGROUND", (0, row_idx), (-1, row_idx), col))
    t.setStyle(TableStyle(s))
    return t

def box(title, body, color=GOLD):
    inner = [P(f"<b>{title}</b>", mk("BoxT", BODY, fontSize=10.5, textColor=color,
                fontName="Helvetica-Bold", alignment=TA_LEFT, spaceAfter=3)),
             P(body, BODY)]
    t = Table([[inner]], colWidths=[16.5*cm])
    t.setStyle(TableStyle([
        ("BOX", (0,0), (-1,-1), 1, color),
        ("BACKGROUND", (0,0), (-1,-1), LIGHT),
        ("LEFTPADDING", (0,0), (-1,-1), 10),
        ("RIGHTPADDING", (0,0), (-1,-1), 10),
        ("TOPPADDING", (0,0), (-1,-1), 8),
        ("BOTTOMPADDING", (0,0), (-1,-1), 8),
    ]))
    return t

def invariant_block():
    t = Table([[P("RHClaimed = false", INVARIANT)],
               [P("HilbertPolyaClaimed = false", INVARIANT)],
               [P("PhysicalClaimed = false", INVARIANT)]],
              colWidths=[16.5*cm])
    t.setStyle(TableStyle([
        ("BOX", (0,0), (-1,-1), 1, RED),
        ("BACKGROUND", (0,0), (-1,-1), colors.HexColor("#FDF2F2")),
        ("LEFTPADDING", (0,0), (-1,-1), 12),
        ("RIGHTPADDING", (0,0), (-1,-1), 12),
        ("TOPPADDING", (0,0), (-1,-1), 9),
        ("BOTTOMPADDING", (0,0), (-1,-1), 9),
        ("LINEABOVE", (0,1), (-1,1), 0.3, MUTED),
        ("LINEABOVE", (0,2), (-1,2), 0.3, MUTED),
    ]))
    return t

def hf(canvas, doc):
    canvas.saveState()
    w, h = A4
    canvas.setFont("Helvetica-Oblique", 8)
    canvas.setFillColor(MUTED)
    canvas.drawString(2*cm, h - 1.2*cm, "Couret-Unification v35.9.1 — Intégrations doctrinales")
    canvas.drawRightString(w - 2*cm, h - 1.2*cm, "RHClaimed = false")
    canvas.setStrokeColor(GOLD); canvas.setLineWidth(0.5)
    canvas.line(2*cm, h - 1.35*cm, w - 2*cm, h - 1.35*cm)
    canvas.setFont("Helvetica", 8); canvas.setFillColor(MUTED)
    canvas.drawCentredString(w/2, 1.1*cm, f"— {canvas.getPageNumber()} —")
    canvas.drawString(2*cm, 1.1*cm, "Pour Bernard Couret (1928–1999, Istres)")
    canvas.drawRightString(w - 2*cm, 1.1*cm, "24 avril 2026")
    canvas.restoreState()

def cover(canvas, doc):
    canvas.saveState()
    w, h = A4
    canvas.setStrokeColor(GOLD); canvas.setLineWidth(1)
    canvas.line(3*cm, h - 3*cm, w - 3*cm, h - 3*cm)
    canvas.line(3*cm, 3*cm, w - 3*cm, 3*cm)
    canvas.setStrokeColor(MUTED); canvas.setLineWidth(0.3)
    canvas.line(3.5*cm, h - 2.8*cm, w - 3.5*cm, h - 2.8*cm)
    canvas.line(3.5*cm, 3.2*cm, w - 3.5*cm, 3.2*cm)
    canvas.restoreState()

# ═══════════════════════════════════════════════════════════════════════════
story = []

# ─── Page de garde ───────────────────────────────────────────────────────
story.append(SP(50))
story.append(P("<b>PROGRAMME COURET–UNIFICATION</b>", mk("TG1", BODY,
    fontSize=13, alignment=TA_CENTER, fontName="Helvetica-Bold",
    textColor=PLATINUM, spaceAfter=4)))
story.append(P("Compagnon du dossier v35.9.1", mk("TG2", BODY,
    fontSize=11, alignment=TA_CENTER, fontName="Helvetica-Oblique",
    textColor=MUTED, spaceAfter=40)))

story.append(P("INTÉGRATIONS", TITLE_BIG))
story.append(P("DOCTRINALES", TITLE_BIG))
story.append(SP(10))
story.append(P("— Registre des impasses, architecture Lean,", mk("TG3", BODY,
    fontSize=12, alignment=TA_CENTER, fontName="Helvetica-Oblique",
    textColor=DIAMOND)))
story.append(P("TimeBridge LTB-0, trois candidats d'algèbre,", mk("TG3b", BODY,
    fontSize=12, alignment=TA_CENTER, fontName="Helvetica-Oblique",
    textColor=DIAMOND)))
story.append(P("ModThirtyChecker FCI —", mk("TG3c", BODY,
    fontSize=12, alignment=TA_CENTER, fontName="Helvetica-Oblique",
    textColor=DIAMOND, spaceAfter=12)))

story.append(SP(12))
story.append(P("Consolidation des dix contributions reçues", TITLE_SUB))
story.append(P("le 24 avril 2026", TITLE_SUB))

story.append(SP(50))
story.append(HRFlowable(width="50%", thickness=0.7, color=GOLD,
    hAlign="CENTER", spaceAfter=18, spaceBefore=8))

story.append(P("<b>Alexandre Couret</b>", mk("TG4", BODY,
    fontSize=13, alignment=TA_CENTER, fontName="Helvetica-Bold",
    textColor=INK, spaceAfter=3)))
story.append(P("SASU CONFIANCE · Rasiguères, France", mk("TG5", BODY,
    fontSize=11, alignment=TA_CENTER, textColor=INK, spaceAfter=3)))
story.append(P("couret-unification.fr", mk("TG6", BODY, fontSize=10,
    alignment=TA_CENTER, fontName="Helvetica-Oblique", textColor=DIAMOND,
    spaceAfter=18)))

story.append(SP(50))
story.append(P("24 avril 2026", mk("TG7", BODY, fontSize=11,
    alignment=TA_CENTER, textColor=MUTED)))

story.append(SP(60))
story.append(HRFlowable(width="35%", thickness=0.3, color=MUTED,
    hAlign="CENTER", spaceAfter=9, spaceBefore=3))
story.append(P("<i>Ce document consolide quatre contributions doctrinales</i>", DEDICACE))
story.append(P("<i>reçues le 24 avril 2026 et les intègre à l'architecture v35.9.1.</i>",
    DEDICACE))
story.append(P("<i>Il est le compagnon strict du dossier Horizons ; il ne le remplace pas.</i>",
    DEDICACE))

story.append(PageBreak())

# ─── Avertissement ───────────────────────────────────────────────────────
story.append(P("Avertissement épistémique", H1))
story.append(bar())

story.append(P(
    "Ce document est le <b>compagnon d'intégration</b> du dossier Horizons "
    "v35.9.1. Il n'expose pas à nouveau les dix horizons de recherche (voir "
    "le PDF Horizons). Il consolide quatre contributions doctrinales reçues "
    "sous forme de dix fichiers le 24 avril 2026 :", BODY))

contrib_list = [
    ["Contribution",                                        "Fichiers concernés",                                 "Nature"],
    ["1. Registre d'auto-falsification",                    "Rapport_Impasses_CouretUnification.md",              "26 impasses (13 A + 13 B)"],
    ["2. Architecture Lean v35.8.8",                        "Ameliorations_Architecture_Thomas.md + Frozen.lean + Active.lean + Meta/SnapshotSentinel.lean",  "7 priorités opérationnelles"],
    ["3. TimeBridge LTB-0 + candidats d'algèbre",           "LTB0_README.md + 2 fichiers Lean + docx 3 candidats", "Calibration B2, Candidat C ouvert"],
    ["4. FCI ModThirtyChecker",                              "ModThirtyChecker_lean__2_.txt",                      "Kernel Lean capteur d'inhibition"],
]
story.append(tbl(contrib_list, [5.5*cm, 6*cm, 5*cm], font=8.5))

story.append(SP(6))
story.append(P(
    "<b>Intégrité du bundle</b>. Les dix fichiers sont inclus tels quels "
    "dans <font face='Courier' size='9'>v35.9.1-complete-bundle.zip</font>. "
    "Ce PDF les synthétise, cartographie leur articulation avec le reste du "
    "programme, et met à jour la roadmap et les horizons concernés.", BODY))

story.append(SP(8))
story.append(invariant_block())

story.append(PageBreak())

# ─── TOC ────────────────────────────────────────────────────────────────
story.append(P("Table des matières", H1))
story.append(bar())

toc = [
    ("Partie I",    "Registre d'auto-falsification — 26 impasses"),
    ("  §I.1",       "Typologie R/C/N/B/A/T"),
    ("  §I.2",       "Tableau synoptique Partie A (A1-A13 documentées)"),
    ("  §I.3",       "Détail narratif des 13 impasses A"),
    ("  §I.4",       "Registre à compléter Partie B (B1-B13)"),
    ("  §I.5",       "Structure Lean RetiredBridges.lean"),
    ("",            ""),
    ("Partie II",   "Architecture Lean v35.8.8 — 7 priorités Thomas"),
    ("  §II.1",      "Diagnostic des points de friction"),
    ("  §II.2",      "Priorité 1 — SnapshotSentinel.lean"),
    ("  §II.3",      "Priorité 2 — Umbrella Frozen / Active segmentée"),
    ("  §II.4",      "Priorités 3-7 — SorryRegistry, quickstart, CI"),
    ("  §II.5",      "Classement impact/coût et plan de déploiement"),
    ("",            ""),
    ("Partie III",  "TimeBridge LTB-0 et trois candidats d'algèbre"),
    ("  §III.1",     "Livraison LTB-0 — trois fichiers Lean à 0 sorry"),
    ("  §III.2",     "Identité B2 : ½ log(7/6) ⟺ 1/7"),
    ("  §III.3",     "Candidat A — algèbre de groupe finie [réfuté]"),
    ("  §III.4",     "Candidat B — produit croisé par P₇ [réfuté]"),
    ("  §III.5",     "Candidat C — Bost-Connes mod 30 [OUVERT]"),
    ("  §III.6",     "Intégration dans Horizon 6"),
    ("",            ""),
    ("Partie IV",   "FCI ModThirtyChecker — capteur d'inhibition"),
    ("  §IV.1",      "Architecture EADX et doctrine never-forces-allow"),
    ("  §IV.2",      "Contenu Lean : projectToG30, empiricalDistribution"),
    ("  §IV.3",      "Séparation stricte FCI ↔ Couret-Unification"),
    ("",            ""),
    ("Partie V",    "Mise à jour — roadmap v35.9.1 intégrée"),
    ("  §V.1",       "Nouvelle sous-question Horizon 6 (Candidat C)"),
    ("  §V.2",       "Deux inconsistances internes à résoudre"),
    ("  §V.3",       "Plan 2026-2029 révisé"),
    ("",            ""),
    ("Annexe",      "Inventaire des 10 fichiers intégrés"),
]
for num, title in toc:
    if num == "":
        story.append(SP(3))
    elif num.startswith("  §"):
        story.append(P(f"&nbsp;&nbsp;&nbsp;&nbsp;<b>{num.strip()}</b>&nbsp;&nbsp;{title}",
            mk("TOCS", BODY, textColor=PLATINUM, spaceAfter=1, fontSize=9.5)))
    else:
        story.append(P(f"<b>{num}</b>&nbsp;&nbsp;{title}", BODY))
        story.append(SP(1))

story.append(PageBreak())

# ═══════════════════════════════════════════════════════════════════════════
# PARTIE I — Registre des impasses
# ═══════════════════════════════════════════════════════════════════════════
story.append(P("Partie I.<br/>Registre d'auto-falsification — 26 impasses", H1))
story.append(bar())

story.append(P(
    "Le <b>Rapport des impasses Couret-Unification</b> (24 avril 2026) est un "
    "document de 581 lignes qui consigne systématiquement les retractations, "
    "corrections, no-go et bugs identifiés au fil du programme. Il sert de "
    "registre d'auto-falsification. Toute erreur publiée, toute route "
    "éliminée et tout artefact détecté y reçoit une entrée typée avec "
    "source conversationnelle, énoncé avant/après, mécanisme de détection, "
    "et leçon méthodologique.", BODY))

story.append(box("Principe doctrinal",
    "Un programme qui ne documente pas ses impasses n'a pas appris à "
    "les éviter. Le registre est la pierre angulaire de "
    "<font face='Courier'>RHClaimed = false</font> : c'est ce qui distingue "
    "une recherche honnête d'une auto-persuasion.", color=NAVY))

# ─── §I.1 Typologie ──────────────────────────────────────────────────────
story.append(P("§I.1. Typologie R/C/N/B/A/T", H2))

typo = [
    ["Code", "Nom",            "Description",                                      "Exemple"],
    ["R",    "Retractation",   "Un résultat annoncé est faussement affirmé",       "Lock 2 résolu → encodé (A3)"],
    ["C",    "Correction",     "Une chaîne argumentative utilise un mauvais outil", "Schur(V) → ‖M‖_HS (A4)"],
    ["N",    "No-go",          "Une route d'attaque est éliminée quantitativement", "5 routes Lock 3 (A5)"],
    ["B",    "Bug",            "Erreur d'implémentation masquant un problème réel", "channel_balance v7.2d (A9)"],
    ["A",    "Artefact",       "Résultat numérique = sous-produit du modèle",       "B2 t_equil v15.2 (A11)"],
    ["T",    "Terminologie",   "Confusion d'objets distincts sous même étiquette",  "M₄ = 15 vs 21 (A8)"],
]
story.append(tbl(typo, [1.2*cm, 2.5*cm, 7.5*cm, 5.3*cm], font=8.5))

# ─── §I.2 Tableau synoptique ─────────────────────────────────────────────
story.append(P("§I.2. Tableau synoptique des 13 impasses documentées (Partie A)", H2))

imp_synopsis = [
    ["#",  "Titre court",                                         "Type", "Date",       "Statut"],
    ["A1", "Spectre Fourier de TC corrigé {3²,1⁴,(−1)²}",         "R",    "mars 2026",  "corrigée"],
    ["A2", "Pas d'extinctions c_χ ; 8 coefficients tous non nuls", "R",    "mars 2026",  "corrigée"],
    ["A3", "« Lock 2 résolu » → « Lock 2 encodé »",                "R",    "mars 2026",  "requalifiée"],
    ["A4", "v17→v18 : Schur(V) → ‖M‖_HS ≤ 0.8495",                 "C",    "mars 2026",  "corrigée"],
    ["A5", "5 routes Lock 3 éliminées N1-N5 (L10)",                "N",    "déc. 2025+", "formalisées"],
    ["A6", "Lock 2 dissous par Hadamard 1893",                    "C tardive","avril 2026","dissout"],
    ["A7", "Bug E=3 à L5 : 11 ∈ TC divise 2310",                  "B+C",  "avril 2026",  "corrigée v28"],
    ["A8", "M₄ = 15 vs 21 (P-ρ² vs Tr(A⁴)/8)",                     "T",    "avril 2026",  "clarifiée"],
    ["A9", "channel_balance_v7.2d : chareval + imprimitivité",     "B",    "avril 2026",  "corrigée"],
    ["A10","V_eff réfute λ=1/√7 scaling brut",                     "R+N",  "avril 2026",  "réfutée"],
    ["A11","B2 t_equil v15.2 : bug dbm_delta3 ignore L",           "A+B",  "24 avril 26", "retirée"],
    ["A12","Candidat C torsion KMS : test spécificité échoue",    "N",    "24 avril 26", "disqualifiée"],
    ["A13","M3 falsifié, trivialité spectrale CRT",                 "N",    "avril 2026",  "réfutée"],
]
story.append(tbl(imp_synopsis, [1*cm, 7.5*cm, 1.5*cm, 2.5*cm, 4*cm], font=8))

# ─── §I.3 Détail narratif des 13 A ───────────────────────────────────────
story.append(PageBreak())
story.append(P("§I.3. Détail narratif — les 13 impasses A", H2))

story.append(P(
    "Chaque entrée est condensée en trois lignes : énoncé erroné, énoncé "
    "correct, leçon. Le rapport source donne le détail complet (mécanisme "
    "de détection, tableaux numériques, URI conversationnelle).", BODY))

story.append(P("<b>A1 — Spectre de Fourier de TC</b> [type R]", H3))
story.append(P(
    "<b>Avant</b> : Spec(A_TC) = {3, 3, 1, 1, 1, 1, 1, 1}, toutes positives.<br/>"
    "<b>Après</b> : Spec(A_TC) = {3², 1⁴, <b>(−1)²</b>} — deux valeurs propres "
    "négatives. L'opérateur n'est pas positif-défini.<br/>"
    "<b>Leçon</b> : une table de valeurs propres sans <font face='Courier'>"
    "native_decide</font> n'est pas un fait Lean, c'est une espérance.", BODY))

story.append(P("<b>A2 — Fausses extinctions spectrales</b> [type R]", H3))
story.append(P(
    "<b>Avant</b> : deux coefficients c_χ s'annulent (caractères quadratiques "
    "mod 3 et mod 5), « TC aveugle aux discriminants 3 et 5 ».<br/>"
    "<b>Après</b> : aucun coefficient ne s'annule. Les 8 valeurs sont "
    "{3/8, 3/8, −1/8, −1/8, 1/8, 1/8, 1/8, 1/8}.<br/>"
    "<b>Leçon</b> : coefficient numériquement petit ≠ coefficient "
    "structurellement nul. Distinction doctrinale, pas rhétorique.", BODY))

story.append(P("<b>A3 — Lock 2 requalifié « encodé » et non « résolu »</b> [type R]", H3))
story.append(P(
    "<b>Avant</b> : « Lock 2 résolu » par décomposition F(s) = Σ c_χ L(s,χ).<br/>"
    "<b>Après</b> : projection sur la base de caractères = fait algébrique "
    "standard, pas un théorème analytique nouveau. Statut correct « encodé ». "
    "Lock 2 sera <i>dissous</i> plus tard par A6, mais par un autre mécanisme.<br/>"
    "<b>Leçon</b> : encodage dans un formalisme ≠ résolution.", BODY))

story.append(P("<b>A4 — Correction v17→v18 : Schur(V) → ‖M‖_HS</b> [type C]", H3))
story.append(P(
    "<b>Avant</b> : test de Schur appliqué directement à V, borné via P(σ).<br/>"
    "<b>Après</b> : ‖V‖_HS diverge à σ = 1/2 (V ∉ S₂). Outil correct : "
    "M = (H₀+I)^(−½)·V·(H₀+I)^(−½), alors ‖M‖_HS ≤ P(3/2) = 0.8495 < 1. "
    "Chaîne KLMN reconstruite.<br/>"
    "<b>Leçon</b> : un test spectral s'applique à un opérateur précis. "
    "Changer d'opérateur de référence change la borne.", BODY))

story.append(P("<b>A5 — Cinq routes éliminées (L10)</b> [type N]", H3))
story.append(P(
    "N1 (multiplicative) : spectre entier vs cible irrationnelle.<br/>"
    "N2 (sinc·χ₃₀) : ratio A/B diverge à 10¹¹.<br/>"
    "N3 (Connes naïf) : γ^(−0.33) vs cible γ^(−1).<br/>"
    "N4 (Berry-Keating) : non-compact, spectre continu.<br/>"
    "N5 (kurtosis-collapse µ_k→δ₁) : M₄ = 21, κ = 7/3 ≠ 1.<br/>"
    "Cristallisé en théorème <font face='Courier'>L10NoGoTheorem.lean</font>.<br/>"
    "<b>Leçon</b> : un no-go chiffré vaut plus qu'un « peut-être ».", BODY))

story.append(P("<b>A6 — Lock 2 dissous comme tautologie Hadamard</b> [type C tardive]", H3))
story.append(P(
    "Chaîne (A) Hadamard 1893 : ξ(s) entière d'ordre 1, genre 1 → "
    "produit de Weierstrass. (B) B₁ = 0 : conséquence algébrique pure de "
    "ξ(s) = ξ(1−s). (C) Appariement ±γ : facteurs exp(z/γ_n)·exp(−z/γ_n) "
    "= 1. Donc si Lock 3 donne Spec(S) = {±1/γ_n}, alors "
    "det₂(I−zS) = (1/ξ(1/2)) · ξ(1/2 + iz) automatiquement. Normalisation "
    "C = 1/ξ(1/2) ≈ 2.01158 vérifiée à 50 chiffres.<br/>"
    "<b>Leçon</b> : un verrou narratif n'est pas toujours un verrou logique. "
    "Le programme se réduit à <b>un seul sorry irréductible</b> "
    "(<font face='Courier'>lock3_operator_exists</font>, équivalent à RH).",
    BODY))

story.append(P("<b>A7 — Bug E = 3 à L5</b> [type B+C]", H3))
story.append(P(
    "<b>Détection</b> : à q = 2310, φ(q) = 480, Parseval = 960 (pas 1440), "
    "E = 2 (pas 3).<br/>"
    "<b>Cause</b> : 11 ∈ TC et 11 divise 2310, donc χ(11) = 0 pour tout "
    "caractère mod 2310.<br/>"
    "<b>Correction</b> : E = 3 est invariant de la <i>tour sûre</i> qui "
    "saute les p ∈ {11, 29}. Pack Lean v28 intègre <font face='Courier'>"
    "29 &lt; p</font>.<br/>"
    "<b>Leçon</b> : vérifier un invariant numériquement au-delà du niveau "
    "où il est conjecturé ; les divisibilités d'éléments de TC par le "
    "modulus sont des obstructions structurelles.", BODY))

story.append(P("<b>A8 — Confusion M₄ : 15 vs 21</b> [type T]", H3))
story.append(P(
    "Les deux nombres sont corrects mais désignent des objets distincts :<br/>"
    "— <b>P − ρ² = 24 − 9 = 15</b> : masse de Parseval non triviale.<br/>"
    "— <b>M₄ = Tr(A⁴)/8 = 168/8 = 21</b> : 4ᵉ moment spectral brut.<br/>"
    "Le ratio (P−ρ²)/M₂² = 15/9 = 5/3, kurtosis brute M₄/M₂² = 21/9 = 7/3. "
    "Réfutation µ_k → δ₁ (entrée N5) utilise κ = 7/3 ≠ 1, reste valide.<br/>"
    "<b>Leçon</b> : deux nombres sous une même étiquette = bug de "
    "terminologie. <font face='Courier'>Kurtosis.lean</font> avec table "
    "explicite résout définitivement.", BODY))

story.append(P("<b>A9 — Bug channel_balance_v7</b> [type B]", H3))
story.append(P(
    "Évolution de trois bugs successifs : "
    "(1) v7.1 : χ_1(n) = if(gcd(n,30)==1, 1, 0) masquait le pôle, "
    "corrigé en χ_1(n) = 1. "
    "(2) v7.2a-c : <font face='Courier'>chareval</font> retourne un rationnel r, "
    "pas exp(2πir). Wrapper : <font face='Courier'>chi(n) = exp(2*Pi*I*chareval(...))</font>. "
    "(3) v7.2d : <font face='Courier'>Mod(4,15)</font> et <font face='Courier'>"
    "Mod(7,15)</font> étaient imprimitifs (conducteur = 5). Remplacement par "
    "<font face='Courier'>Mod(14,15)</font> et <font face='Courier'>Mod(8,15)</font> "
    "primitifs.<br/>"
    "<b>Leçon</b> : les caractères modulaires doivent être vérifiés pour "
    "primitivité avant toute L-fonction.", BODY))

story.append(P("<b>A10 — Réfutation du pont V_eff : λ = 1/√7 brut</b> [type R+N]", H3))
story.append(P(
    "<b>Verdict</b> : V_eff / (1/7) loin de 1. Proximité 3/8 ≈ 1/√7 est "
    "une coïncidence numérique, pas un mécanisme. Diagnostic théorique : "
    "V(χ) ~ C_RS · log(q_χ), donc V_eff · dim diverge logarithmiquement.<br/>"
    "<b>Conséquences</b> : λ = 1/√7 comme invariant universel brut est "
    "réfuté. 1/√7 ≈ 0.378 et 1/φ(30) = 0.375 sont proches mais distincts "
    "(écart 0.8 %). La géométrie sur Δ⁷ et λ_k = 1/√(k−1) <i>restent</i> "
    "comme résultats géométriques. Pont local-global → biais de Chebyshev, "
    "pas RH.<br/>"
    "<b>Leçon</b> : passer d'une constante mystique à un objet vérifiable "
    "est une épuration, pas un recul.", BODY))

story.append(P("<b>A11 — B2 t_equil v15.2 : bug dbm_delta3(L, t_equil)</b> [type A+B]", H3))
story.append(P(
    "<b>Détection (24 avril 2026)</b> : le code "
    "<font face='Courier'>dbm_delta3(L, t_equil)</font> prend L en argument "
    "<i>mais ne l'utilise jamais</i> dans le corps. Pour toute L, Δ₃_model "
    "est la même constante.<br/>"
    "<b>Conséquence</b> : le « fit sur Δ₃(L) » de v15.2 ajustait une "
    "constante à une courbe, avec χ²/dof = 0.93 = régression dégénérée. "
    "Le t_equil ≈ 0.077 était un artefact de modèle mal défini.<br/>"
    "<b>Reconstruction correcte</b> : avec Δ₃_GUE(L) = (1/π²)·log(L)+…, les "
    "500 premiers zéros sont essentiellement GUE pur. Le modèle "
    "Poisson/GUE avec λ² = 1/7 prédit Δ₃ ~ 10× trop grand. Réfuté.<br/>"
    "<b>Statut révisé</b> : B2-v15.2 retiré. L'identité t* = ½ log(7/6) "
    "reste <i>valide comme identité algébrique conditionnelle</i>.<br/>"
    "<b>Leçon</b> : un χ²/dof = 0.93 peut masquer un bug de spécification. "
    "Réimplémenter depuis la formule théorique est non-négociable.", BODY))

story.append(P("<b>A12 — Candidat C « torsion KMS mod 30 » disqualifié</b> [type N]", H3))
story.append(P(
    "<b>Test</b> : scan des quotients <font face='Courier'>dim(H_sub)/dim(H_M)</font> "
    "pour M ∈ {6, 10, 14, 30, 42, 210, 2310}.<br/>"
    "<b>Résultat</b> : ratio (φ(M) − 1)/φ(M) apparaît <i>mécaniquement</i> "
    "pour chaque M. Aucune singularité à M = 30.<br/>"
    "<b>Verdict</b> : variantes mod M produisent constantes analogues sans "
    "spécificité → falsifié. Branches C3-B et C3-C fermées.<br/>"
    "<b>Reste ouvert</b> : peut-il exister une observable <i>non "
    "dimensionnelle</i> qui sélectionne réellement M = 30 ? (cf. Partie III)<br/>"
    "<b>Leçon</b> : ratio qui coïncide mécaniquement sur modules voisins = "
    "faux signal. Test de spécificité inter-modules = garde-fou minimal.",
    BODY))

story.append(P("<b>A13 — M3 falsifié, trivialité spectrale CRT</b> [type N]", H3))
story.append(P(
    "<b>Formule fermée établie</b> : L_k = 2 + (4 + 2(−1)^k)/3^k (prouvé "
    "<font face='Courier'>native_decide</font>).<br/>"
    "<b>Mismatch structurel</b> : L_k · a(k) ~ O(1) vs Σ 2/γ_n^(2k) ~ "
    "O(14^(−2k)) — décroissance exponentielle incompatible.<br/>"
    "<b>Conclusion</b> : la tour primoriale ne produit pas les zéros de ζ. "
    "Transport CRT ajoute des zéros triviaux (à c_χ = 0) mais pas de "
    "structure spectrale non triviale. Ratios entre valeurs propres "
    "non-nulles invariants par CRT : tour = zoom trivial sur L3.<br/>"
    "<b>Leçon</b> : un facteur d'échelle qui diverge exponentiellement sur "
    "plusieurs niveaux est un signal décisif.", BODY))

story.append(PageBreak())

# ─── §I.4 Partie B ───────────────────────────────────────────────────────
story.append(P("§I.4. Registre à compléter — 13 impasses B", H2))

story.append(P(
    "Les 13 entrées B sont référencées dans le registre mais non "
    "documentables depuis l'historique conversationnel. Elles attendent "
    "d'être remplies par Couret à partir des manuscrits Bernard, des notes "
    "Thomas, des logs PARI/GP et des archives JR Consulting.", BODY))

partB = [
    ["#",   "Titre court",                                         "Source requise"],
    ["B1",  "Cosmologie λ-φ (Phase 0, abandon 2025)",               "manuscrits Couret"],
    ["B2",  "Projet Factory-432 (abandon Phase 0, 2025)",            "manuscrits Couret"],
    ["B3",  "Conjecture λ_n = 1/√(n+1) (Phase 0)",                    "manuscrits Bernard"],
    ["B4",  "Correction L-κ* : σ_c ≈ 0.86",                          "canal Gemini/GPT"],
    ["B5",  "Falsification Δ(q) ≠ a·log log q + b, err. 84.9%",      "rapport Thomas / logs PARI"],
    ["B6",  "Obstruction symplectique J² = −I en dim impaire",       "SymplecticObstruction.lean"],
    ["B7",  "Audit Lean 4 : 30 erreurs catégorisées A/B/C/D",        "session 6 avril 2026"],
    ["B8",  "7 overclaims du site web corrigés",                     "snapshot site pre-audit"],
    ["B9",  "Abandon de la « tour enrichie »",                        "canal parallèle"],
    ["B10", "Dérive logarithmique globale falsifiée",                 "scripts PARI/Python"],
    ["B11", "Anisotropie R = 0.75, d_eff ≈ 5.15",                     "chat Claude 7 avril 2026"],
    ["B12", "Propagation Parseval L5 = 960 aux scripts externes",     "audit scripts Thomas/Expert"],
    ["B13", "Corrections Tesla : κ=0, comptage 59 vs 63",             "script Tesla v1"],
]
story.append(tbl(partB, [1*cm, 10*cm, 5.5*cm], font=8.5))

# ─── §I.5 RetiredBridges.lean ────────────────────────────────────────────
story.append(P("§I.5. Formalisation Lean : RetiredBridges.lean", H2))

story.append(P(
    "Le rapport propose un enum typé pour figer le statut de chaque entrée "
    "au type-check Lean :", BODY))

story.extend(code_block := code(
    "-- CouretUnification/Meta/RetiredBridges.lean (proposé)\n"
    "inductive EmpiricalBridgeStatus\n"
    "  | active           -- A5 routes ouvertes (Connes adélique, Hecke enrichie)\n"
    "  | falsified        -- A10 : λ=1/√7 ; A13 : M3\n"
    "  | retired_artifact -- A11 : B2-v15.2 plateau\n"
    "  | conjectural      -- DBM mésoscopique\n"
    "  | corrected        -- A4, A7, A8, A9\n"
    "  | dissolved        -- A3 (Lock 2 encodé), A6 (Lock 2 Hadamard)\n"
    "  | eliminated       -- A5 (5 routes), A12, B6, B9"))

story.append(P(
    "Chaque entrée A1-A13 et B1-B13 devient une définition typée avec sa "
    "leçon attachée. Un théorème <font face='Courier'>all_retired_bridges_"
    "documented</font> pourrait ensuite exiger une entrée par impasse — "
    "garantie au type-check que le registre est tenu à jour.", BODY))

story.append(box("Recommandation d'intégration",
    "Ajouter <font face='Courier'>RetiredBridges.lean</font> dans "
    "<font face='Courier'>CouretUnification/Meta/</font> comme fichier "
    "Frozen-éligible (0 sorry, structures pures). Importé par "
    "<font face='Courier'>Frozen.lean</font>. Devient alors la preuve "
    "au type-check que le registre d'auto-falsification est exhaustif.",
    color=GREEN))

story.append(PageBreak())

# ═══════════════════════════════════════════════════════════════════════════
# PARTIE II — Architecture Thomas
# ═══════════════════════════════════════════════════════════════════════════
story.append(P("Partie II.<br/>Architecture Lean v35.8.8 — 7 priorités Thomas", H1))
story.append(bar())

story.append(P(
    "La note <b>Améliorations d'architecture — pour Thomas</b> (371 lignes) "
    "propose 7 améliorations ciblées pour réduire la friction opérationnelle "
    "de Thomas lors des cycles Mathlib et des fronts actifs. Aucune refonte "
    "fondamentale proposée ; l'architecture v35.8.8 (<font face='Courier'>"
    "Meta/Logic/C</font> bien séparées, BUILD.md exhaustif, DAG explicite) "
    "est jugée saine.", BODY))

# ─── §II.1 Diagnostic ────────────────────────────────────────────────────
story.append(P("§II.1. Diagnostic des points de friction", H2))

story.append(P(
    "Trois scénarios où Thomas perd du temps aujourd'hui :", BODY))
story.append(bullet(
    "<b>Mathlib bouge</b> et casse un lemme snapshot-dépendant. La casse se "
    "propage à 7 points dans 5 fichiers. Debug aveugle fichier par fichier."))
story.append(bullet(
    "<b>Un front actif</b> (H3, AnalyticHorizon) ajoute un sorry ou une "
    "régression → <i>toute</i> l'umbrella <font face='Courier'>"
    "CouretUnification.lean</font> (17 modules en chaîne linéaire) échoue. "
    "Thomas ne peut plus vérifier que le core reste compilable."))
story.append(bullet(
    "<b>Un nouveau fichier arrive</b> (comme TimeBridge LTB-0) et doit être "
    "validé rapidement sans casser le reste."))

# ─── §II.2 Priorité 1 ────────────────────────────────────────────────────
story.append(P("§II.2. Priorité 1 — Meta/SnapshotSentinel.lean [très haut impact, 30 min]", H2))

story.append(P(
    "<b>Principe</b> : concentrer tous les lemmes Mathlib fragiles dans un "
    "unique fichier sentinelle avec <font face='Courier'>example</font> "
    "triviaux qui les invoquent. Si ce fichier casse, Thomas sait "
    "immédiatement quel lemme a changé, quels fichiers vont casser en "
    "cascade, et quel fallback documenté appliquer.", BODY))

story.append(P("Temps de diagnostic : ~30 min aveugle → ~2 min ciblé.", BODY))

story.append(P("<b>Les 10 sentinelles</b> (fichier livré, autonome) :", H3))

sentinelles = [
    ["Code",   "Lemme Mathlib",                           "Utilisé par",                    "Fallback"],
    ["S-01",   "Real.rpow_le_one_of_one_le_of_nonpos",    "H3/LocalFactor",                 "via rpow_neg + one_div_le_one"],
    ["S-02",   "Real.rpow_nonneg",                        "H3/LocalFactor",                 "stable historiquement"],
    ["S-03",   "Real.one_le_sqrt",                        "H3/LocalFactor",                 "Real.sqrt_one_le_iff"],
    ["S-04",   "Real.neg_one_le_cos / cos_le_one",        "H3/LocalFactor",                 "hautement stable"],
    ["S-05",   "Real.log_inv",                            "TimeBridge/B2Calibration",        "Real.log_div"],
    ["S-05bis","Real.log_inv (forme ratio)",              "TimeBridge (fallback)",           "direct"],
    ["S-06",   "Real.exp_log",                            "TimeBridge/B2Calibration",        "très stable"],
    ["S-07",   "ArithmeticFunction.moebius",              "H3/MoebiusBridge",                "stable"],
    ["S-08",   "Nat.squarefree_mul",                      "H3/SquarefreeSupport",            "Nat.Squarefree.mul"],
    ["S-09",   "Complex.abs / ‖·‖",                       "Det2Transport",                   "deprecation → ‖·‖"],
]
story.append(tbl(sentinelles, [1.5*cm, 5.5*cm, 4*cm, 5.5*cm], font=8))

story.append(P(
    "<b>Règle d'or</b> : ce fichier ne doit <b>jamais</b> être importé par un "
    "autre fichier du dépôt. Il est purement diagnostique. Commande de test :",
    BODY))
story.extend(code("lake build CouretUnification.Meta.SnapshotSentinel"))
story.append(P(
    "La référence <font face='Courier'>snapshotReferenceVersion := \"Mathlib "
    "tag attendu v4.15.0-compatible\"</font> doit être mise à jour à chaque "
    "bump de lean-toolchain.", BODY))

# ─── §II.3 Priorité 2 ────────────────────────────────────────────────────
story.append(P("§II.3. Priorité 2 — Umbrella segmentée Frozen / Active [haut impact, 15 min]", H2))

story.append(P(
    "<b>Principe</b> : remplacer l'umbrella unique par deux umbrellas ciblées.",
    BODY))

story.append(P("<b>CouretUnification/Frozen.lean</b> (nouveau) — 10 fichiers à 0 sorry, ne doit JAMAIS casser :", H3))
story.extend(code(
    "import CouretUnification.Meta.Doctrine\n"
    "import CouretUnification.Logic.OpenLocks\n"
    "import CouretUnification.Logic.EulerBridgeInfiniteCompat\n"
    "import CouretUnification.Logic.C3Weak_Gram\n"
    "import CouretUnification.Logic.ChiralityFinite\n"
    "import CouretUnification.Logic.ChiralityLinear\n"
    "import CouretUnification.Logic.L6Interface\n"
    "import CouretUnification.Logic.L6Bridge\n"
    "import CouretUnification.Logic.H3.LocalFactor\n"
    "import CouretUnification.Logic.H3.CriticalLineTransferSpec\n"
    "-- À activer après livraison LTB-0 :\n"
    "-- import CouretUnification.Logic.TimeBridge.Basic\n"
    "-- import CouretUnification.Logic.TimeBridge.B2Calibration\n"
    "-- import CouretUnification.Logic.TimeBridge.ModularFlowSpec"))

story.append(P("<b>CouretUnification/Active.lean</b> (nouveau) — 7 fichiers, 9-11 sorries documentés :", H3))
story.extend(code(
    "import CouretUnification.Frozen  -- hérite du socle\n"
    "import CouretUnification.Logic.L6Analytic              -- 1 sorry ANALYTIC\n"
    "import CouretUnification.Logic.L6RatioEstimateDerived  -- 1 sorry\n"
    "import CouretUnification.Logic.L10NoGoTheorem          -- 3 sorry\n"
    "import CouretUnification.Logic.H3.SquarefreeSupport    -- 1 sorry OBSOLETE\n"
    "import CouretUnification.Logic.H3.SquarefreeDensity    -- 3 sorry\n"
    "import CouretUnification.Logic.H3.MoebiusBridge        -- 1 sorry SNAPSHOT\n"
    "import CouretUnification.AnalyticHorizon.Det2Transport -- 1 sorry DOCTRINAL"))

story.append(P("<b>CouretUnification.lean</b> (simplifié) :", H3))
story.extend(code("import CouretUnification.Frozen\nimport CouretUnification.Active"))

story.append(box("Règle d'or",
    "Aucun fichier de <font face='Courier'>Frozen</font> ne peut importer "
    "un fichier de <font face='Courier'>Active</font>. Direction stricte : "
    "Frozen → Active, jamais l'inverse. Si un ancien fichier Frozen a besoin "
    "d'un fichier Active, il faut d'abord le rétrograder.", color=ORANGE))

story.append(P("<b>Conséquences opérationnelles</b> :", H3))
story.append(bullet(
    "<font face='Courier'>lake build CouretUnification.Frozen</font> = sanity "
    "check express (~5 min avec cache). Doit passer sur chaque commit."))
story.append(bullet(
    "<font face='Courier'>lake build CouretUnification.Active</font> = vérif "
    "des fronts actifs. Peut échouer temporairement."))
story.append(bullet(
    "<font face='Courier'>lake build CouretUnification</font> = tout."))

story.append(PageBreak())

# ─── §II.4 Priorités 3-7 ─────────────────────────────────────────────────
story.append(P("§II.4. Priorités 3 à 7 — SorryRegistry, quickstart, FileIdentity, obligations typées, CI", H2))

story.append(P("<b>Priorité 3 — Meta/SorryRegistry.lean</b> [haut impact, 1 h]", H3))
story.append(P(
    "Aujourd'hui les 11 sorries sont listés en Markdown BUILD.md, non "
    "vérifiable. Rien n'empêche un 12ᵉ sans mise à jour. "
    "<b>Solution</b> : structure typée qui énumère les sorries attendus :",
    BODY))

sorry_registry = [
    ["#",  "Fichier",                                  "Catégorie",       "Rationale"],
    ["1",  "L6Analytic.lean",                          "analytic",        "stirling_remainder_bound"],
    ["2",  "L6RatioEstimateDerived.lean",              "analytic",        "assembly analytique"],
    ["3",  "L10NoGoTheorem.lean",                      "analytic",        "specTarget_conceptual"],
    ["4",  "L10NoGoTheorem.lean",                      "upstream",        "Mathlib API irrationnalité"],
    ["5",  "L10NoGoTheorem.lean",                      "upstream",        "Mathlib API Dirichlet"],
    ["6",  "H3/SquarefreeSupport.lean",                "obsolete",        "hors chemin critique"],
    ["7",  "H3/SquarefreeDensity.lean",                "analytic",        "error_term_isBigO"],
    ["8",  "H3/SquarefreeDensity.lean",                "analytic",        "squarefreeCount_ge_half"],
    ["9",  "H3/SquarefreeDensity.lean",                "analytic",        "cible 6/π²"],
    ["10", "H3/MoebiusBridge.lean",                    "snapshot",        "sommabilité μ à s=2"],
    ["11", "Det2Transport.lean",                       "doctrinal",       "sorry unique du fichier"],
]
story.append(tbl(sorry_registry, [0.7*cm, 4.5*cm, 2.5*cm, 8.8*cm], font=7.5))

story.append(P("Théorème invariant : <font face='Courier'>expectedSorries.length = 11</font>. "
    "Si le comptage bash diverge du compte Lean, bug détecté.", BODY))

story.append(P("<b>Priorité 4 — scripts/quickstart.sh</b> [moyen-haut impact, 15 min]", H3))
story.append(P(
    "Un script unique qui fait le chemin rapide : "
    "<font face='Courier'>cache get → SnapshotSentinel → Frozen → "
    "invariant RH</font>. Bénéfice : un nouveau contributeur peut dire "
    "« mon dépôt est vivant » en 10 min, même si les fronts actifs évoluent.",
    BODY))

story.append(P("<b>Priorité 5 — FileIdentity partout</b> [moyen impact, 1-2 h]", H3))
story.append(P(
    "Chaque fichier reçoit un <font face='Courier'>def fileIdentity : "
    "FileIdentity := ⟨...⟩</font> à la fin (5 lignes/fichier). Bénéfice : "
    "un théorème <font face='Courier'>all_respect_rh_invariant</font> "
    "vérifie en une ligne <i>pour tous les fichiers</i> qu'aucun n'a "
    "<font face='Courier'>rhClaimed = true</font>.", BODY))

story.append(P("<b>Priorité 6 — Obligations typées pour sorries doctrinaux</b> [moyen impact, 30 min]", H3))
story.append(P(
    "Transformer un sorry en <i>obligation typée</i>. Dans "
    "<font face='Courier'>Det2Transport.lean</font>, les trois hypothèses "
    "H1/H2/H3 deviennent champs d'une <font face='Courier'>DefectObligations"
    "</font>. Le sorry résiduel devient mécanique, pas doctrinal. "
    "Cette technique vaut d'être généralisée aux autres sorries analytiques.",
    BODY))

story.append(P("<b>Priorité 7 — CI GitHub Actions minimale</b> [haut impact moyen terme, 30 min]", H3))
story.append(P(
    "<font face='Courier'>.github/workflows/build.yml</font> avec deux jobs : "
    "<font face='Courier'>frozen</font> (garde absolue, casse = merge bloqué) "
    "et <font face='Courier'>full</font> (<font face='Courier'>"
    "continue-on-error: true</font>, signal sans bloquer). Suppose la "
    "priorité 2 (umbrella segmentée) en place.", BODY))

# ─── §II.5 Plan ──────────────────────────────────────────────────────────
story.append(P("§II.5. Classement impact/coût et plan de déploiement", H2))

ranking = [
    ["#",   "Amélioration",                          "Coût (h)", "Impact", "Livré dans bundle v35.9.1-complete"],
    ["1",   "SnapshotSentinel.lean",                 "0.5",      "★★★★",   "OUI (Meta/SnapshotSentinel.lean)"],
    ["2",   "Umbrella Frozen / Active",              "0.25",     "★★★★",   "OUI (Frozen.lean + Active.lean)"],
    ["3",   "SorryRegistry.lean",                    "1.0",      "★★★",    "non (esquisse, à rédiger)"],
    ["4",   "scripts/quickstart.sh",                 "0.25",     "★★★",    "non (esquisse)"],
    ["5",   "FileIdentity partout",                  "1.5",      "★★",     "non"],
    ["6",   "Obligations typées Det2",               "0.5",      "★★",     "partiel (Det2Obligations.lean)"],
    ["7",   "CI GitHub Actions",                     "0.5",      "★★★",    "non (esquisse)"],
]
story.append(tbl(ranking, [0.7*cm, 5*cm, 1.5*cm, 1.5*cm, 7.8*cm], font=8))

story.append(P(
    "<b>Total pour les 4 premières</b> : ~2 heures de travail Thomas, "
    "économies cumulatives à chaque cycle Mathlib. Les priorités 1 et 2 "
    "sont <b>directement intégrées</b> dans le bundle v35.9.1-complete.", BODY))

story.append(box("Ce qui n'est PAS recommandé",
    "1. Refactor Core/ ↔ Logic/ (architecture saine).<br/>"
    "2. Unifier AnalyticHorizon et Logic (différence doctrinale réelle).<br/>"
    "3. Migrer sorries vers axiomes (sorries préférables tant qu'en cours).<br/>"
    "4. Supprimer les 11 sorries d'un coup (attendent vrais résultats mathématiques).",
    color=RED))

story.append(PageBreak())

# ═══════════════════════════════════════════════════════════════════════════
# PARTIE III — TimeBridge LTB-0 + 3 candidats
# ═══════════════════════════════════════════════════════════════════════════
story.append(P("Partie III.<br/>TimeBridge LTB-0 et trois candidats d'algèbre", H1))
story.append(bar())

# ─── §III.1 ──────────────────────────────────────────────────────────────
story.append(P("§III.1. Livraison LTB-0 — trois fichiers Lean à 0 sorry", H2))

story.append(P(
    "La couche <font face='Courier'>Logic/TimeBridge/</font> est livrée en "
    "version <b>LTB-0</b> — entièrement typée, aucun <font face='Courier'>"
    "String</font> dans les structures de spec. Adresse le blocage identifié "
    "dans la BUILD v35.8.8 (« structures dont les champs sont principalement "
    "<font face='Courier'>String</font>, non intégrables »).", BODY))

ltb0 = [
    ["Fichier",                    "Sorries", "Rôle"],
    ["Basic.lean",                 "0",       "Drapeaux doctrinaux RH/HP/Phys = False ; marqueur openProblem ; enum TimeRegister (8 registres)"],
    ["B2Calibration.lean",         "0",       "Identité ½ log(7/6) ⟺ 1/7 prouvée ; structures B2Run et B2DiagnosticTable"],
    ["ModularFlowSpec.lean",       "0",       "Spec corrélateur modulaire ; prédicat IsLogarithmicGrowth ; conjecture B1 en openProblem"],
]
story.append(tbl(ltb0, [4*cm, 1.5*cm, 11*cm], font=8.5))

story.append(P("<b>DAG d'imports</b> : chaîne linéaire isolée :", H3))
story.extend(code(
    "Mathlib.Tactic\n"
    "   ↑\n"
    "Logic/TimeBridge/Basic              [0 sorry]\n"
    "   ↑\n"
    "Logic/TimeBridge/B2Calibration      [0 sorry]\n"
    "   ↑                                      ↑\n"
    "Logic/TimeBridge/ModularFlowSpec    [0 sorry]"))

story.append(P(
    "<b>Aucun fichier Core/ ou AnalyticHorizon/ ne les importe</b>. TimeBridge "
    "est une couche de spécification, pas une dépendance de preuve. "
    "Construction comme cible séparée dans le build.", BODY))

# ─── §III.2 Identité B2 ──────────────────────────────────────────────────
story.append(P("§III.2. L'identité B2 : ½ log(7/6) ⟺ 1/7", H2))

story.append(P(
    "Le théorème central <font face='Courier'>B2_calibration_identity</font> "
    "prouve :", BODY))
story.extend(code(
    "theorem B2_calibration_identity :\n"
    "    1 - Real.exp (-2 * t_canonical) = lambda_squared_target\n"
    "  où  t_canonical := (1/2) * Real.log (7/6)\n"
    "      lambda_squared_target := 1/7"))

story.append(P(
    "Vérification numérique à 15 décimales : "
    "<font face='Courier'>½ ln(7/6) = 0.077075339913629</font>, puis "
    "<font face='Courier'>1 − exp(−2·t*) = 1/7 = 0.142857142857143</font> "
    "(identique bit-à-bit).", BODY))

story.append(box("Avertissement doctrinal",
    "Cette identité est <b>algébriquement triviale</b>. Elle ne démontre "
    "RIEN du programme. Elle consigne seulement le point canonique autour "
    "duquel les runs numériques B2 mesurent un écart. "
    "<br/><br/>"
    "La question non triviale <b>reste ouverte</b> : pourquoi λ² = 1/7 "
    "apparaît-il dans la dynamique des zéros ? Cette question dépend de "
    "la géométrie de Fisher-Rao sur Δ⁷ (registre spectral) et/ou du "
    "coefficient du corrélateur modulaire (registre 3).", color=NAVY))

# ─── §III.3-III.5 : 3 candidats ──────────────────────────────────────────
story.append(P("§III.3. Candidat A — algèbre de groupe finie ℂ[(ℤ/30ℤ)×] [RÉFUTÉ]", H2))

story.append(P(
    "<b>Définition</b> : M_A := ℂ[G₃₀], abélienne finie de dimension 8, "
    "donc M_A ≅ ℂ⁸ comme C*-algèbre commutative.", BODY))

story.append(P(
    "<b>Verdict</b> : pour toute algèbre commutative M et tout état fidèle φ, "
    "le flux modulaire est identiquement trivial : σ_t^φ = id. Corollaire "
    "immédiat de la commutativité.", BODY))

story.append(box("Conclusion Candidat A",
    "<b>Réfuté</b>. Aucun flux modulaire non trivial n'est possible. "
    "A fortiori, aucun temps canonique ne peut émerger. "
    "<br/><br/>"
    "<b>Leçon</b> : toute tentative de lire λ² = 1/7 comme engendrant un "
    "flux doit nécessairement invoquer une structure <i>non commutative</i>. "
    "Un passage canonique à une algèbre non commutative requiert un choix "
    "supplémentaire.", color=RED))

story.append(P("§III.4. Candidat B — produit croisé par P₇ [RÉFUTÉ]", H2))

story.append(P(
    "<b>Définition</b> : M_B := M_A ⋊_α ℤ où α(n) = P₇ⁿ, avec P₇ "
    "automorphisme de G₃₀ d'ordre 4.", BODY))

story.append(P(
    "<b>Structure</b> : par dualité de Takai, chaque orbite de ℤ/4ℤ "
    "donne C(ℤ/4ℤ) ⋊ ℤ ≅ M₄(ℂ) ⊗ C(𝕋). Somme directe des deux orbites "
    "(Orb_A = {1, 7, 19, 13} ; Orb_B = {11, 17, 29, 23}) donne :", BODY))
story.extend(code("M_B ≅ ( M₄(ℂ) ⊗ C(𝕋) ) ⊕ ( M₄(ℂ) ⊗ C(𝕋) )"))

story.append(P(
    "Dans la représentation régulière, M_B'' est homogène <b>de type I</b>. "
    "Pour un état fidèle normal φ sur une algèbre de type I, le flux "
    "modulaire σ_t^φ est <b>intérieur</b>, implémenté par un opérateur "
    "positif à spectre <b>discret</b>.", BODY))

story.append(P(
    "<b>Peut-on ajuster les λᵢ pour obtenir t* ?</b> Techniquement oui, "
    "en choisissant λᵢ/λⱼ = 7/6 pour un couple (i,j) bien placé. Mais "
    "c'est exactement un choix externe non canonique.", BODY))

story.append(box("Conclusion Candidat B",
    "<b>Réfuté</b>. M_B est de type I, flux intérieur à spectre discret. "
    "Toute apparition de t* exige un choix supplémentaire non imposé par "
    "la structure.<br/><br/>"
    "<b>Leçon</b> : pour obtenir un flux modulaire non-trivialement "
    "canonique, il faut une algèbre de <b>type III</b>. Les produits "
    "croisés finis-sur-ℤ par actions de groupes finis ne suffisent pas.",
    color=RED))

story.append(PageBreak())

story.append(P("§III.5. Candidat C — Bost-Connes mod 30 restreint [OUVERT]", H2))

story.append(box("STATUT : OUVERT — nouvelle piste de recherche",
    "Ce candidat est la seule piste parmi les trois qui n'a pas été "
    "réfutée. Il devient la <b>piste concrète principale pour l'Horizon 6</b> "
    "(construction d'un opérateur Hilbert-Pólya) du dossier Horizons v35.9.1. "
    "La sous-question technique précise est consignée comme programme "
    "prospectif dans le dossier Expert.", color=GREEN))

story.append(P("<b>Motivation</b>", H3))
story.append(P(
    "Le système de Bost-Connes (1995) est l'exemple canonique d'algèbre "
    "arithmétique dont le flux modulaire encode une information "
    "arithmétique. Des variantes mod N ont été étudiées "
    "(Laca-Raeburn, Cuntz-Li, Laca-van Frankenhuysen). Pour N = 30, une "
    "construction naturelle restreinte aux premiers p ∤ 30.", BODY))

story.append(P("<b>Construction candidate</b>", H3))
story.extend(code(
    "ℕ×_(30) := { n ∈ ℕ× : gcd(n, 30) = 1 }\n"
    "X_30    := Ẑ_(30) × G_30   (espace arithmétique adapté)\n"
    "A_30    := C(X_30) ⋊ ℕ×_(30)   (ℕ×_(30) agit par multiplication)\n"
    "φ_β     := état de Gibbs à température inverse β (condition KMS)"))

story.append(P("<b>Structure attendue par analogie</b>", H3))
story.append(bullet(
    "A_30 devrait avoir un <i>unique</i> état KMS pour β ≤ 1 (phase symétrique)."))
story.append(bullet(
    "Pour β > 1 : brisure de symétrie spontanée, états KMS indexés par "
    "les caractères de G_30."))
story.append(bullet(
    "Fonction de partition : "
    "Z_{30}(β) = ∏_{p∤30} (1 − p^{−β})^{−1} = ζ(β) · (1−2^{−β})(1−3^{−β})(1−5^{−β})."))
story.append(bullet(
    "Type du facteur GNS en phase symétrique : <b>type III_1</b>. C'est "
    "exactement la classe qui peut porter un flux modulaire non trivial "
    "à spectre continu."))

story.append(P("<b>Où apparaîtrait t* = ½ log(7/6) ?</b>", H3))
story.append(P(
    "Trois voies candidates testées sans succès pour l'instant :", BODY))
story.append(bullet(
    "<b>(a) Rapport de fonctions de partition</b> : ½ log(Z_{30}(β₁) / "
    "Z_{30}(β₂)) à valeurs naturelles de β."))
story.append(bullet(
    "<b>(b) Quotients spectraux</b> : pour certaines représentations via "
    "caractères de G_30, matrice modulaire locale ρ à spectre fini."))
story.append(bullet(
    "<b>(c) Température critique d'un sous-système</b> : sous-système "
    "engendré par G_30 et multiplication par 7 seulement. Sous-système "
    "arithmétique mod 7, susceptible de porter une transition KMS à "
    "température liée à log 7."))

story.append(P(
    "<b>Honnêteté méthodologique</b> : les trois voies n'ont pas produit "
    "d'apparition canonique de ½ log(7/6). Cela <i>ne prouve pas</i> son "
    "absence. Il reste des constructions non explorées.", BODY))

story.append(P("<b>La sous-question technique précise à trancher</b>", H3))

story.append(box("Programme prospectif TimeBridge",
    "Dans le système Bost-Connes mod 30 restreint avec l'état KMS de "
    "Gibbs à β = 1, existe-t-il une observable canonique "
    "<i>non dimensionnelle</i> du sous-système {1, 7, 49, 343, …} ⊂ "
    "ℕ×_(30) telle que son espérance sous l'état KMS extrême non "
    "symétrique fasse apparaître ½ log(7/6) comme temps propre ?<br/><br/>"
    "<b>Technique, bornée, décidable par calcul explicite</b>. Peut être "
    "attaquée en 20-30 pages de travail sérieux par un spécialiste des "
    "systèmes Bost-Connes.", color=VIOLET))

# ─── §III.6 Intégration ──────────────────────────────────────────────────
story.append(P("§III.6. Intégration dans Horizon 6 du dossier Horizons v35.9.1", H2))

story.append(P(
    "Le dossier Horizons v35.9.1 listait pour l'<b>Horizon 6 (construction "
    "d'un opérateur HP concret)</b> quatre pistes : Sonine poursuivie (A), "
    "de Branges reprise critique (B), Berry-Keating régularisée (C), "
    "Connes adélique (D).", BODY))

story.append(P(
    "La note algèbre arithmétique <b>ajoute une cinquième piste concrète</b>, "
    "qui est plus précise que la piste D générique :", BODY))

story.append(box("Nouvelle piste E — Bost-Connes mod 30 restreint",
    "Variante explicite de l'approche Connes adélique, formulée sur le "
    "module 30 avec corps cyclotomique ℚ(ζ_30). Produit effectivement un "
    "facteur de type III_1 avec structure KMS riche. La sous-question "
    "technique est <b>bornée et explicite</b> — peut produire un test "
    "falsifiable en 20-30 pages.<br/><br/>"
    "Cette piste gagne sur l'option D générique par sa <i>spécificité au "
    "programme Couret-Unification</i> : elle articule directement la "
    "structure mod 30 (TC, G_30, corps ℚ(ζ_30)) avec la machinerie "
    "Bost-Connes établie.", color=VIOLET))

story.append(P(
    "<b>Recommandation</b> : retenir cette piste comme <i>programme "
    "prospectif TimeBridge</i> dans une annexe du dossier Expert, sans "
    "la faire entrer dans le dossier principal de résultats certifiés. "
    "Le statut <font face='Courier'>openProblem True</font> du fichier "
    "Lean <font face='Courier'>ModularFlowSpec.lean</font> encode "
    "précisément cette distinction au type-check.", BODY))

story.append(PageBreak())

# ═══════════════════════════════════════════════════════════════════════════
# PARTIE IV — ModThirtyChecker
# ═══════════════════════════════════════════════════════════════════════════
story.append(P("Partie IV.<br/>FCI ModThirtyChecker — capteur d'inhibition", H1))
story.append(bar())

story.append(P(
    "Le fichier <font face='Courier'>FCI/ModThirtyChecker.lean</font> est le "
    "kernel Lean du bloc E (Extraction) du pipeline EADX (Extract/Analyze/"
    "Decide/eXecute) de l'architecture FCI. Il détecte les biais "
    "statistiques mod 30 dans un flux d'entiers (clés RSA, sorties PRNG, "
    "nonces cryptographiques) en comparant la signature spectrale empirique "
    "au spectre de référence <b>prouvé</b> du graphe de Cayley "
    "Cay(G_30, TC).", BODY))

# ─── §IV.1 ──────────────────────────────────────────────────────────────
story.append(P("§IV.1. Architecture EADX et doctrine never-forces-allow", H2))

story.append(box("Contrat doctrinal FCI",
    "<b>Ce module est un CAPTEUR D'INHIBITION, jamais sur le chemin "
    "d'autorisation.</b> Conformément à la doctrine FCI : il peut forcer "
    "INHIBIT, jamais forcer ALLOW. Sa défaillance (faux négatif, crash, "
    "overflow) ne viole jamais les propriétés P1–P5 : elle dégrade la "
    "disponibilité, pas la sûreté.<br/><br/>"
    "C'est l'asymétrie fondamentale qui rend FCI <i>compatible safety case</i> "
    "DAL/SIL : le capteur ne peut qu'ajouter du refus, jamais retirer du refus.",
    color=NAVY))

story.append(P("<b>Flux opérationnel du bloc E</b>", H3))
story.extend(code(
    "Entrée   : Sample (List ℕ, taille bornée ≤ 65536 par WCET)\n"
    "  ↓\n"
    "projectToG30 : ℕ → Option G30   (ignore non-coprimes à 30)\n"
    "  ↓\n"
    "empiricalDistribution : Sample → G30 → ℕ\n"
    "  ↓\n"
    "comparaison au spectre de référence {3², 1⁴, (−1)²}\n"
    "  ↓\n"
    "score χ² / KS\n"
    "  ↓\n"
    "décision : INHIBIT si seuil dépassé, PASS sinon\n"
    "           (jamais forcer ALLOW, même si test OK)"))

story.append(P("<b>Statut épistémique par primitive</b>", H3))

epist = [
    ["Code",  "Primitive",                               "Étiquette", "Signification"],
    ["[P]",   "projections arithmétiques",                "prouvé",    "calcul fini, decidable par native_decide"],
    ["[P]",   "comparaison au spectre de référence",       "prouvé",    "égalité décidable sur ℚ"],
    ["[N]",   "seuils de détection",                       "numérique", "calibrés empiriquement, non prouvés optimaux"],
    ["[C]",   "théorème de liaison avec P1 (refuse-by-default)", "conditionnel", "à rédiger"],
]
story.append(tbl(epist, [1*cm, 7*cm, 2*cm, 6.5*cm], font=8.5))

# ─── §IV.2 ──────────────────────────────────────────────────────────────
story.append(P("§IV.2. Contenu Lean — les fonctions-clés", H2))

story.append(P("<b>Type d'entrée borné WCET</b>", H3))
story.extend(code(
    "structure Sample where\n"
    "  data    : List ℕ\n"
    "  bounded : data.length ≤ 65536\n"
    "  deriving Repr"))

story.append(P(
    "Le choix <font face='Courier'>List ℕ</font> plutôt que "
    "<font face='Courier'>Array</font> est délibéré : il force la taille "
    "bornée à l'interface, évitant les pièges WCET du bloc E.", BODY))

story.append(P("<b>Projection arithmétique</b>", H3))
story.extend(code(
    "def projectToG30 (n : ℕ) : Option G30 :=\n"
    "  let r := n % 30\n"
    "  if h : Nat.gcd r 30 = 1 then\n"
    "    some ⟨r, r, by sorry, by sorry⟩\n"
    "  else\n"
    "    none"))

story.append(P(
    "Renvoie <font face='Courier'>none</font> si l'entier n'est pas "
    "coprime à 30. Seules les 8 classes {1, 7, 11, 13, 17, 19, 23, 29} "
    "sont admissibles. Les deux <font face='Courier'>sorry</font> sont "
    "[P] prouvables par <font face='Courier'>decide</font> une fois CRT30 "
    "compilé.", BODY))

story.append(P("<b>Distribution empirique</b>", H3))
story.extend(code(
    "def empiricalDistribution (s : Sample) : G30 → ℕ :=\n"
    "  fun g =>\n"
    "    s.data.foldl (fun acc n =>\n"
    "      match projectToG30 n with\n"
    "      | some g' => if g' = g then acc + 1 else acc\n"
    "      | none    => acc) 0"))

# ─── §IV.3 ──────────────────────────────────────────────────────────────
story.append(P("§IV.3. Séparation stricte FCI ↔ Couret-Unification", H2))

story.append(box("Règle architecturale inviolable",
    "FCI (application industrielle) et Couret-Unification (recherche math.NT) "
    "partagent la SASU CONFIANCE et Alexandre Couret comme directeur "
    "scientifique, mais leurs livrables, leurs audiences et leurs canaux "
    "sont <b>strictement séparés</b>.<br/><br/>"
    "<b>FCI/ModThirtyChecker.lean importe</b> : FiniteCore.CRT30, "
    "FiniteCore.Characters30, FiniteCore.CayleyTC — c'est-à-dire le noyau "
    "fini mod 30 <i>prouvé</i>, indépendant de toute hypothèse sur RH.<br/><br/>"
    "<b>FCI ne prétend PAS démontrer RH</b>. Il utilise un résultat "
    "algébrique stable (spectre {3², 1⁴, (−1)²} certifié "
    "<font face='Courier'>native_decide</font>) comme référence de "
    "comparaison statistique.", color=GOLD))

story.append(P(
    "Cette séparation est capitale pour la stratégie commerciale FCI : "
    "l'invariant <font face='Courier'>RHClaimed = false</font> du "
    "programme Couret-Unification ne bloque <b>en rien</b> la "
    "commercialisation FCI, puisque FCI s'appuie sur le noyau fini et pas "
    "sur la conjecture globale.", BODY))

story.append(PageBreak())

# ═══════════════════════════════════════════════════════════════════════════
# PARTIE V — Mise à jour roadmap
# ═══════════════════════════════════════════════════════════════════════════
story.append(P("Partie V.<br/>Mise à jour — roadmap v35.9.1 intégrée", H1))
story.append(bar())

# ─── §V.1 ────────────────────────────────────────────────────────────────
story.append(P("§V.1. Nouvelle sous-question Horizon 6 (Candidat C)", H2))

story.append(P(
    "Le dossier Horizons v35.9.1 liste 10 horizons. L'intégration des "
    "contributions du 24 avril 2026 affine l'Horizon 6 (opérateur HP "
    "concret) avec une <b>5ᵉ piste explicite</b> qui remplace la piste D "
    "(Connes adélique générique) par une variante précise :", BODY))

horizon6 = [
    ["Piste", "Description",                                            "Statut"],
    ["A",     "Sonine poursuivie (S_{1/2, 30})",                         "en cours"],
    ["B",     "de Branges reprise critique",                              "stratégie reprise"],
    ["C",     "Berry-Keating régularisée",                                "spéculatif"],
    ["D",     "Connes adélique générique",                                "lourd"],
    ["E",     "Bost-Connes mod 30 restreint (NOUVEAU)",                   "piste OUVERTE précise"],
]
story.append(tbl(horizon6, [1*cm, 10*cm, 5.5*cm], font=8.5))

story.append(P(
    "<b>Avantage de la piste E</b> : elle articule directement les données "
    "du programme (mod 30, TC, G_30, corps ℚ(ζ_30)) avec la machinerie "
    "Bost-Connes <i>établie</i>. La sous-question est bornée, technique, "
    "décidable par calcul explicite — donc <b>falsifiable</b>.", BODY))

# ─── §V.2 ────────────────────────────────────────────────────────────────
story.append(P("§V.2. Deux inconsistances internes à résoudre avant présentation externe", H2))

story.append(box("Flag de cohérence",
    "L'intégration des 10 fichiers révèle deux points qui doivent être "
    "tranchés avant la présentation Norwich de juin 2026 :", color=ORANGE))

story.append(P("<b>Inconsistance 1 — M₄ : 15 vs 21</b>", H3))
story.append(P(
    "L'entrée A8 du rapport des impasses clarifie définitivement : "
    "P − ρ² = <b>15</b> (masse Parseval non triviale), M₄ = Tr(A⁴)/8 = "
    "<b>21</b> (4ᵉ moment spectral brut). La synthèse Expert, la note "
    "TimeBridge et les documents antérieurs utilisent les deux nombres. "
    "<b>Action</b> : audit textuel du dossier Expert avec remplacement "
    "systématique « M₄ = 15 » → « P − ρ² = 15 » et vérification explicite "
    "de chaque occurrence de « M₄ » pour distinguer les deux sens.", BODY))

story.append(P("<b>Inconsistance 2 — C3 : ambigu entre fermé et ouvert</b>", H3))
story.append(P(
    "Le programme mentionne C3 sous deux statuts apparemment "
    "contradictoires : dans la chaîne C0-C5 (Gold/Diamond/Platinum) "
    "certains documents le présentent comme « fermé » ; dans le rapport "
    "des impasses (A12), les branches C3-B et C3-C sont <i>disqualifiées</i> "
    "par test de spécificité. <b>Action</b> : trancher si C3 est :", BODY))
story.append(bullet("(a) fermé au niveau Gold mais ouvert au niveau Diamond/Platinum,"))
story.append(bullet("(b) partiellement fermé (seule la partie dimensionnelle est disqualifiée),"))
story.append(bullet("(c) entièrement ouvert avec C3-B et C3-C retirées."))
story.append(P(
    "La clarification doit être inscrite dans la chaîne C0-C5 du site "
    "<font face='Courier'>couret-unification.fr</font> et dans le dossier "
    "Expert v2.", BODY))

# ─── §V.3 ────────────────────────────────────────────────────────────────
story.append(P("§V.3. Plan 2026-2029 révisé avec intégrations", H2))

plan = [
    ["Période",            "Action",                                                               "Livrable"],
    ["Mai 2026",           "Build v35.9.1-complete vert chez Thomas + audit M₄/C3",                 "Repo clean"],
    ["Mai 2026",           "Rédaction RetiredBridges.lean à partir du rapport d'impasses",          "Meta/RetiredBridges.lean"],
    ["Juin 2026",          "Workshop Norwich : présentation + LMFDB alignment",                     "Communication externe"],
    ["Juillet 2026",       "Rapport Expert v2 avec M₄/C3 corrigés + Candidat C documenté",          "Doc validée"],
    ["Août 2026",          "Priorités 3-7 architecture Thomas (SorryRegistry, CI, quickstart)",     "Infrastructure"],
    ["Septembre 2026",     "Préprint Sophie Germain χ²=243 (résultat autonome)",                     "arXiv math.NT"],
    ["T4 2026",            "Horizon 1 (vonMangoldt) en Lean → PR Mathlib",                          "Contribution Mathlib"],
    ["2027",               "Horizons 2-3 (RvM, digamma/Stirling)",                                  "2 PR Mathlib"],
    ["2028-2029",          "Horizon 4 : formule explicite Guinand-Weil formalisée",                  "Soumission Annals"],
    ["2029+",              "Horizons 5-7 ; exploration Candidat C Bost-Connes mod 30",              "Thèse HDR + annexe"],
    ["?",                  "Horizons 8-10 : Lock 3, auto-adjonction complète, local-global",        "Pas planifiable"],
]
story.append(tbl(plan, [2.5*cm, 8*cm, 6*cm], font=8))

story.append(P(
    "<b>Note finale</b> : RHClaimed reste <font face='Courier'>false</font> "
    "jusqu'à certificat Lean sans sorry. Aucun des livrables 2026-2028 ne "
    "prétend démontrer RH. Le Candidat C Bost-Connes mod 30 est une "
    "<i>piste prospective</i>, pas une promesse.", BODY))

story.append(PageBreak())

# ═══════════════════════════════════════════════════════════════════════════
# ANNEXE — Inventaire
# ═══════════════════════════════════════════════════════════════════════════
story.append(P("Annexe.<br/>Inventaire des 10 fichiers intégrés", H1))
story.append(bar())

story.append(P(
    "Les 10 fichiers reçus le 24 avril 2026 sont tous inclus dans "
    "<font face='Courier'>v35.9.1-complete-bundle.zip</font>. Voici leur "
    "mapping exact dans l'arborescence du dépôt :", BODY))

mapping = [
    ["Fichier reçu",                                           "Destination dans le dépôt"],
    ["Rapport_Impasses_CouretUnification.md",                  "docs/Rapport_Impasses.md"],
    ["Ameliorations_Architecture_Thomas.md",                   "docs/Ameliorations_Architecture_Thomas.md"],
    ["LTB0_README.md",                                          "docs/LTB0_README.md"],
    ["Algebre_arithmetique_flux_modulaire_30.docx",            "docs/Algebre_arithmetique_flux_modulaire_30.docx"],
    ["Meta_SnapshotSentinel_lean.txt",                          "lean/CouretUnification/Meta/SnapshotSentinel.lean"],
    ["CouretUnification_Frozen_lean.txt",                       "lean/CouretUnification/Frozen.lean"],
    ["CouretUnification_Active_lean.txt",                       "lean/CouretUnification/Active.lean"],
    ["TimeBridge_B2Calibration_lean.txt",                       "lean/CouretUnification/Logic/TimeBridge/B2Calibration.lean"],
    ["TimeBridge_ModularFlowSpec_lean.txt",                     "lean/CouretUnification/Logic/TimeBridge/ModularFlowSpec.lean"],
    ["ModThirtyChecker_lean__2_.txt",                            "lean/CouretUnification/FCI/ModThirtyChecker.lean"],
]
story.append(tbl(mapping, [7.5*cm, 9*cm], font=7.5))

story.append(P(
    "<b>Fichiers Lean v35.9.1 déjà produits la session précédente, également inclus</b> :", BODY))

ancient = [
    ["Fichier",                                          "Statut"],
    ["Meta/ProofJurisdiction.lean",                      "Frozen (0 sorry)"],
    ["Logic/ExplicitFormula/TestPair.lean",              "Frozen (0 sorry)"],
    ["Logic/ExplicitFormula/ArithmeticWeight.lean",      "Frozen (0 sorry)"],
    ["Logic/ExplicitFormula/PrimeSide.lean",             "Frozen (0 sorry, 3 théorèmes prouvés)"],
    ["Logic/ExplicitFormula/TraceObject.lean",           "Frozen (0 sorry)"],
    ["Logic/ExplicitFormula/ExplicitFormulaBridge.lean", "Frozen (0 sorry)"],
    ["Logic/ExplicitFormula/ZeroCounting.lean",           "Frozen (0 sorry)"],
    ["Logic/ExplicitFormula/ArchimedeanSide.lean",        "Frozen (0 sorry)"],
    ["Logic/H3/HPCertificate.lean",                      "Frozen (0 sorry)"],
    ["AnalyticHorizon/Det2Obligations.lean",              "Frozen (0 sorry)"],
    ["AnalyticHorizon/Det2Transport.lean",                "Active (1 sorry d'instanciation)"],
]
story.append(tbl(ancient, [10.5*cm, 6*cm], font=8))

story.append(P(
    "<b>Script d'audit inclus</b> : <font face='Courier'>scripts/check_frozen_"
    "invariants.sh</font> (vérifie 0 axiome, 0 constante, sorries tracés).", BODY))

# ─── Clôture ─────────────────────────────────────────────────────────────
story.append(SP(25))
story.append(P("— Clôture —", mk("End", BODY,
    fontSize=15, alignment=TA_CENTER, fontName="Helvetica-Bold",
    textColor=NAVY, spaceAfter=18)))

story.append(P(
    "Les dix fichiers reçus le 24 avril 2026 sont maintenant intégrés à "
    "l'architecture v35.9.1. Quatre contributions doctrinales distinctes "
    "ont été consolidées :", BODY))

story.append(P(
    "<b>1. Le registre d'auto-falsification</b> transforme le programme "
    "d'un ensemble de résultats en une <i>pratique de recherche traçable</i>. "
    "Chaque impasse devient un repère doctrinal.", BODY))

story.append(P(
    "<b>2. Les 7 priorités d'architecture Thomas</b> réduisent la friction "
    "opérationnelle sans modifier la doctrine. Deux sont déjà livrées "
    "(SnapshotSentinel, umbrella Frozen/Active).", BODY))

story.append(P(
    "<b>3. TimeBridge LTB-0 + les trois candidats d'algèbre</b> donnent un "
    "squelette typé pour la couche temps modulaire, et identifient une "
    "nouvelle piste concrète (Bost-Connes mod 30) pour l'Horizon 6.", BODY))

story.append(P(
    "<b>4. Le kernel FCI ModThirtyChecker</b> établit le pont clair entre "
    "le noyau fini mod 30 prouvé et l'application industrielle, sans "
    "mélanger les narrations.", BODY))

story.append(SP(20))
story.append(box("Phrase doctrinale finale",
    "<i>Prouver ce qui est prouvable. Corriger ce qui est faux. "
    "Nommer ce qui est ouvert.</i><br/><br/>"
    "L'intégration v35.9.1 n'ajoute aucune prétention nouvelle. Elle "
    "rend visibles et typées les structures déjà acquises, documente "
    "les impasses déjà traversées, et cartographie proprement la seule "
    "piste ouverte qui émerge du travail (Candidat C). C'est une "
    "<i>mise en ordre</i>, pas une avancée — et c'est exactement la "
    "posture qui protège le programme contre ses propres illusions.",
    color=NAVY))

story.append(SP(25))
story.append(HRFlowable(width="40%", thickness=0.5, color=GOLD,
    hAlign="CENTER", spaceBefore=6, spaceAfter=14))

story.append(P("<i>Pour Bernard Couret (1928–1999, Istres).</i>", DEDICACE))
story.append(P("<i>Le registre d'auto-falsification — dix impasses nommées,</i>", DEDICACE))
story.append(P("<i>dix fichiers intégrés, une seule piste qui reste vraiment ouverte —</i>", DEDICACE))
story.append(P("<i>est l'exacte discipline qu'il tenait dans ses cahiers.</i>", DEDICACE))

story.append(SP(25))
story.append(invariant_block())

doc = SimpleDocTemplate(
    "Attic/Dossier_Couret_Unification_RH_HP_v35.9.1_Integrations.pdf",
    pagesize=A4,
    leftMargin=2*cm, rightMargin=2*cm,
    topMargin=2*cm, bottomMargin=2*cm,
    title="Couret-Unification v35.9.1 — Intégrations doctrinales",
    author="Alexandre Couret",
    subject="Compagnon du dossier Horizons v35.9.1 : consolidation des 10 fichiers du 24 avril 2026",
    keywords="Couret-Unification, impasses, architecture Lean, TimeBridge, Bost-Connes, FCI ModThirtyChecker",
)
doc.build(story, onFirstPage=cover, onLaterPages=hf)

import os
size = os.path.getsize("Attic/Dossier_Couret_Unification_RH_HP_v35.9.1_Integrations.pdf")
print(f"OK : PDF généré — {size:,} bytes ({size/1024:.1f} KB)")
