require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem20721 (b : El bool) (a : El bool) (h1 : Prf (= a F)) : Prf (= (= (∨ F b) (⇒ (¬ b) F)) (= (∨ a b) (⇒ (¬ b) a)));
