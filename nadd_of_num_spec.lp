require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1268738 : Prf (∀ (λ k : El num, (= (nadd_of_num k) (mk_nadd (λ n : El num, (* k n))))));
