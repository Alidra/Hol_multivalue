require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1111462_term_abbrevs;
require open hol-light.thm1111460_spec;
require open hol-light.thm1111461_spec;
opaque symbol lem1111462 [A] (s : El (fun num A)) : Prf (= (term0 A s) (@NIL A)) ≔ EQ_MP (@lem1111461 A s) (@lem1111460 A s);
