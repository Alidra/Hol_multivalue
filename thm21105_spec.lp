require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem21105 (p : El bool) (h1 : Prf (= p T)) : Prf (= (⇒ p (¬ p)) (¬ p));
