require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1277879 : Prf (∀ (λ x : El nadd, (∀ (λ y : El nadd, (= (dest_nadd (nadd_mul x y)) (λ n : El num, (dest_nadd x (dest_nadd y n))))))));
