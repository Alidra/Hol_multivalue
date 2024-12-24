require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1032730 (p : El bool) (q : El bool) : Prf (⇒ (¬ p) (⇒ (= (¬ q) p) q));
