require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm515674_term_abbrevs;
require open hol-light.thm515614_spec;
opaque symbol lem515673 : Prf term0 ≔ ∧ₑ₁ (@lem515614);
opaque symbol lem515674 (n : El num) : Prf (term1 n) ≔ (@lem515673) n;
