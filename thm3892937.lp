require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3892937_term_abbrevs;
require open hol-light.thm3888988_spec;
opaque symbol lem3892937 [_100554] (b : El _100554) (a : El _100554) (cs : El (fun _100554 bool)) (P : El bool) : Prf (term0 _100554 b a cs P) ≔ ∧ₑ₂ (@lem3888988 _100554 b a cs P);
