require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem4211 (q : El bool) (q' : El bool) (p : El bool) (p' : El bool) (h1 : Prf (= p p')) : Prf (⇒ (⇒ p' (= q q')) (= (⇒ p q) (⇒ p' q')));
