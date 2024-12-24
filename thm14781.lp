require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm14781_term_abbrevs;
opaque symbol lem14781 [_2963] (g : El bool) (t : El _2963) (e : El _2963) (g' : El bool) (t' : El _2963) (e' : El _2963) : Prf (= (term0 _2963 g t e g' t' e') (term0 _2963 g t e g' t' e')) ≔ REFL (term0 _2963 g t e g' t' e');
