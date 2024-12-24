require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm516897_term_abbrevs;
opaque symbol lem516897 (m : El num) : Prf (= (term0 m) (= (<= m _0) (= m _0))) ≔ REFL (term0 m);
