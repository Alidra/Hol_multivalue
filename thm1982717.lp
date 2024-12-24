require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982717_term_abbrevs;
require open hol-light.thm1982714_spec;
opaque symbol lem1982717 (m : El real) : Prf (= (real_add m m) (term0 m)) ≔ ∧ₑ₁ (@lem1982714 m (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
