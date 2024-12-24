require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem21529 (b : El bool) (a : El bool) (h1 : Prf (= a T)) : Prf (= (⇒ (= T b) (∨ b (¬ T))) (⇒ (= a b) (∨ b (¬ a))));
