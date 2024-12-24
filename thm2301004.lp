require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2301004_term_abbrevs;
require open hol-light.thm2300962_spec;
require open hol-light.thm2301003_spec;
opaque symbol lem2301004 (n : El int) (m : El int) (p : El int) : Prf (term0 n m p) ≔ ∧ᵢ (@lem2301003 m n p) (@lem2300962 n m p);
