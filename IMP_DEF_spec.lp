require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem9 : Prf (= ⇒ (λ p : El bool, (λ q : El bool, (= (∧ p q) p))));
