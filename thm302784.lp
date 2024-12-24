require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm302784_term_abbrevs;
require open hol-light.thm302628_spec;
require open hol-light.thm302782_spec;
opaque symbol lem302784 (m : El num) (n : El num) : Prf (= (= m n) (= (+ m m) (term0 n))) ≔ EQ_MP (@lem302628 m n) (@lem302782 m n);
