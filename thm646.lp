require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm646_term_abbrevs;
require open hol-light.thm628_spec;
require open hol-light.thm645_spec;
opaque symbol lem646 (p : El bool) (q : El bool) : Prf (term0 p q) ≔ ∧ᵢ (@lem628 p) (@lem645 p q);
