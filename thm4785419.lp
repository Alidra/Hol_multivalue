require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm4785419_term_abbrevs;
opaque symbol lem4785419 [A] : Prf (= (@set_of_list A) (term0 A)) ≔ @set_of_list_def A;
