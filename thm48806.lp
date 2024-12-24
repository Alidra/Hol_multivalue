require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm48806_term_abbrevs;
opaque symbol lem48806 [A] (a : El A) (b : El A) : Prf (= (term0 A a b) (= (= a b) ((@GEQ A) a b))) ≔ REFL (term0 A a b);
