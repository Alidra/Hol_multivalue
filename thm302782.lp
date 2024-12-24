require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm302782_term_abbrevs;
require open hol-light.thm302684_spec;
require open hol-light.thm302741_spec;
opaque symbol lem302782 (m : El num) (n : El num) : Prf (= (= m n) (= (term0 m) (term0 n))) ≔ EQ_MP (@lem302684 m n) (@lem302741 m n);
