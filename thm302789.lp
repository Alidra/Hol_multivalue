require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm302789_term_abbrevs;
require open hol-light.thm302598_spec;
require open hol-light.thm302784_spec;
opaque symbol lem302789 (m : El num) (n : El num) : Prf (= (= m n) (= (BIT0 m) (term0 n))) ≔ EQ_MP (@lem302598 m n) (@lem302784 m n);
