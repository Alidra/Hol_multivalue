require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1105743_term_abbrevs;
require open hol-light.thm1105741_spec;
require open hol-light.thm1105742_spec;
opaque symbol lem1105743 [_25569] (l : El (list _25569)) : Prf (= (term0 _25569 l) ((@HD _25569) l)) ≔ EQ_MP (@lem1105742 _25569 l) (@lem1105741 _25569 l);
