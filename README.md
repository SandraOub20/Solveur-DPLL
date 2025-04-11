# Solveur DPLL (Mini-Projet Logique)

Projet réalisé dans le cadre du mini-projet de logique à l’Université Paris Cité (2024-2025).  
L'objectif est d’implémenter un solveur récursif pour le problème de satisfiabilité (SAT) basé sur l’algorithme DPLL en OCaml.

## Fonctions implémentées

- `simplifie` : simplification des clauses selon un littéral.  
- `unitaire` : détection de clauses unitaires.  
- `pur` : détection de littéraux purs.  
- `solveur_dpll_rec` : solveur récursif principal.

## Compilation

```bash
make
```

Exécution

```bash
./dpll fichiers_tests/sudoku-4x4.cnf
```
