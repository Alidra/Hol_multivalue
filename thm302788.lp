require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm302788_term_abbrevs;
require open hol-light.thm302608_spec;
require open hol-light.thm302783_spec;
opaque symbol lem302788 (m : El num) (n : El num) : Prf (= (= m n) (= (BIT1 m) (term0 n))) ≔ EQ_MP (@lem302608 m n) (@lem302783 m n);
