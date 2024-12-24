require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2530573_term_abbrevs;
require open hol-light.thm2528714_spec;
require open hol-light.thm2529651_spec;
opaque symbol lem2530573 (p : El int) (m : El int) (n : El int) : Prf (term0 p m n) ≔ (@lem2529651 p m n) (@lem2528714 m n p);
