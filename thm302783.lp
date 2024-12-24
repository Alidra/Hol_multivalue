require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm302783_term_abbrevs;
require open hol-light.thm302666_spec;
require open hol-light.thm302781_spec;
opaque symbol lem302783 (m : El num) (n : El num) : Prf (= (= m n) (= (term0 m) (term1 n))) ≔ EQ_MP (@lem302666 m n) (@lem302781 m n);
