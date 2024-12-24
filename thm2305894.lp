require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2305894_term_abbrevs;
require open hol-light.thm2305852_spec;
require open hol-light.thm2305893_spec;
opaque symbol lem2305894 (n : El int) (m : El int) (p : El int) : Prf (term0 n m p) ≔ ∧ᵢ (@lem2305893 m n p) (@lem2305852 n m p);
