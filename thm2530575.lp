require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2530575_term_abbrevs;
require open hol-light.thm2528727_spec;
require open hol-light.thm2530573_spec;
opaque symbol lem2530575 (p : El int) (m : El int) (n : El int) : Prf (= (term0 m p n) (rem m n)) ≔ EQ_MP (@lem2528727 p m n) (@lem2530573 p m n);
