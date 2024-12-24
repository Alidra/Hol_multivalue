require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem20669 (p : El bool) (q : El bool) : Prf (∧ (= (∨ p p) p) (= (∨ p (∨ p q)) (∨ p q)));
