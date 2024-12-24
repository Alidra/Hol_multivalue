require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1073376_term_abbrevs;
opaque symbol lem1073376 [A B] (x : El A) (a : El A) (y : El B) (b : El B) : Prf (= (term0 A B x a y b) (= (= ((@̦‚ A B) x y) ((@̦‚ A B) a b)) (term1 A B x a y b))) ≔ REFL (term0 A B x a y b);
