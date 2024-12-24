require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1347548 : Prf (∃ (λ h : El (fun real hreal), (∃ (λ r : El (fun hreal real), (∧ (∀ (λ x : El hreal, (= (h (r x)) x))) (∧ (∀ (λ x : El real, (⇒ (real_le (real_of_num (NUMERAL _0)) x) (= (r (h x)) x)))) (∧ (∀ (λ x : El hreal, (real_le (real_of_num (NUMERAL _0)) (r x)))) (∀ (λ x : El hreal, (∀ (λ y : El hreal, (= (hreal_le x y) (real_le (r x) (r y))))))))))))));
