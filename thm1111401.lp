require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1111401_term_abbrevs;
opaque symbol lem1111401 [A] : Prf (= (@list_of_seq A) (term0 A)) ≔ @list_of_seq_def A;
