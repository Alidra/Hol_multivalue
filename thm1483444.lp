require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483444_term_abbrevs;
require open hol-light.thm1483441_spec;
opaque symbol lem1483444 (m : El real) : Prf (= (real_add m m) (term0 m)) ≔ ∧ₑ₁ (@lem1483441 m (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
