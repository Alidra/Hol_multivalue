require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm647_term_abbrevs;
require open hol-light.thm618_spec;
require open hol-light.thm646_spec;
opaque symbol lem647 (r : El bool) (p : El bool) (q : El bool) : Prf (term0 r p q) ≔ ∧ᵢ (@lem618 q p r) (@lem646 p q);
