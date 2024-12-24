require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1276766 : Prf (∀ (λ x : El nadd, (∀ (λ y : El nadd, (= (nadd_mul x y) (mk_nadd (λ n : El num, (dest_nadd x (dest_nadd y n)))))))));
