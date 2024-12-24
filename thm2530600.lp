require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2530600_term_abbrevs;
require open hol-light.thm2530575_spec;
opaque symbol lem2530595 (m : El int) (n : El int) : Prf (term0 m n) ≔ λ p : El int, (@lem2530575 p m n);
opaque symbol lem2530600 (m : El int) : Prf (term1 m) ≔ λ n : El int, (@lem2530595 m n);
