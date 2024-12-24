require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm15220_term_abbrevs;
require open hol-light.thm14821_spec;
require open hol-light.thm14995_spec;
opaque symbol lem15220 [_2963] (t : El _2963) (e : El _2963) (g' : El bool) (t' : El _2963) (e' : El _2963) (g : El bool) (h1 : Prf (= g T)) : Prf (term0 _2963 g t e g' t' e') ≔ EQ_MP (@lem14821 _2963 t e g' t' e' g h1) (@lem14995 _2963 t e g' t' e');
