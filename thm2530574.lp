require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2530574_term_abbrevs;
require open hol-light.thm2528731_spec;
require open hol-light.thm2530572_spec;
opaque symbol lem2530574 (n : El int) (m : El int) (p : El int) : Prf (= (term0 m n p) (rem m p)) ≔ EQ_MP (@lem2528731 n m p) (@lem2530572 n m p);
