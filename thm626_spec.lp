require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem626 (p : El bool) : Prf (∧ (⇒ (∧ p p) p) (⇒ p (∧ p p)));
