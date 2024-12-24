require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1268972 : Prf (∀ (λ k : El num, (= (dest_nadd (nadd_of_num k)) (λ n : El num, (* k n)))));
