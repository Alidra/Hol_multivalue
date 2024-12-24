require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982773_term_abbrevs;
require open hol-light.thm1982770_spec;
opaque symbol lem1982773 (x : El real) (y : El real) (q : El num) : Prf (= (term0 x y q) (term1 x y q)) ≔ ∧ₑ₁ (@lem1982770 (@el num) y (@el real) x q);
