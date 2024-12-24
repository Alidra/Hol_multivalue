require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.INT_WOP_term_abbrevs;
require open hol-light.thm2338993_spec;
require open hol-light.thm2339318_spec;
opaque symbol lem2339319 (P : El (fun int bool)) : Prf (= (term0 P) (term1 P)) ≔ EQ_MP (@lem2338993 P) (@lem2339318 P);
