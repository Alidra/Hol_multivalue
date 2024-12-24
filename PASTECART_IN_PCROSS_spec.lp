require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem8004229 [_141927 _141928 _141929] : Prf (∀ (λ s : El (fun (cart _141927 _141928) bool), (∀ (λ t : El (fun (cart _141927 _141929) bool), (∀ (λ x : El (cart _141927 _141928), (∀ (λ y : El (cart _141927 _141929), (= ((@IN (cart _141927 (finite_sum _141928 _141929))) ((@pastecart _141927 _141928 _141929) x y) ((@PCROSS _141927 _141928 _141929) s t)) (∧ ((@IN (cart _141927 _141928)) x s) ((@IN (cart _141927 _141929)) y t)))))))))));
