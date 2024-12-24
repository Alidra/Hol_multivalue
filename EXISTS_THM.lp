require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.EXISTS_THM_term_abbrevs;
require open hol-light.thm9261_spec;
require open hol-light.thm9306_spec;
opaque symbol lem9307 [A] : Prf (= (@∃ A) (term0 A)) ≔ (@lem9261 A) (@lem9306 A);
