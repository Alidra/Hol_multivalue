require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1346990 : Prf (∃ (λ r : El (fun hreal real), (∧ (∀ (λ x : El real, (= (real_le (real_of_num (NUMERAL _0)) x) (∃ (λ y : El hreal, (= x (r y))))))) (∀ (λ y : El hreal, (∀ (λ z : El hreal, (= (hreal_le y z) (real_le (r y) (r z))))))))));
