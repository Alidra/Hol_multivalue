require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem646 (p : El bool) (q : El bool) : Prf (∧ (= (∧ p p) p) (= (∧ p (∧ p q)) (∧ p q)));
