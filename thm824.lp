require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm824_term_abbrevs;
require open hol-light.thm806_spec;
require open hol-light.thm823_spec;
opaque symbol lem824 (p : El bool) (q : El bool) : Prf (term0 p q) ≔ ∧ᵢ (@lem806 p) (@lem823 p q);
