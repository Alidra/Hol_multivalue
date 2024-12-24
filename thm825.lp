require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm825_term_abbrevs;
require open hol-light.thm795_spec;
require open hol-light.thm824_spec;
opaque symbol lem825 (r : El bool) (p : El bool) (q : El bool) : Prf (term0 r p q) ≔ ∧ᵢ (@lem795 q p r) (@lem824 p q);
