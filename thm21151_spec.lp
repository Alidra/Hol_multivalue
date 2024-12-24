require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem21151 (p : El bool) (h1 : Prf (= p F)) : Prf (= (= (⇒ (¬ F) F) F) (= (⇒ (¬ p) p) p));
