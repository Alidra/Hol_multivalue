require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1318767_term_abbrevs;
opaque symbol lem1318767 (x : El nadd) (y : El nadd) : Prf (= (term0 x y) (= (nadd_eq x y) (= (term1 x) (term1 y)))) ≔ REFL (term0 x y);
