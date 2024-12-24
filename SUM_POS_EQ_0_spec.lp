require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7114167 [_132718] : Prf (∀ (λ f : El (fun _132718 real), (∀ (λ s : El (fun _132718 bool), (⇒ (∧ ((@FINITE _132718) s) (∧ (∀ (λ x : El _132718, (⇒ ((@IN _132718) x s) (real_le (real_of_num (NUMERAL _0)) (f x))))) (= ((@sum _132718) s f) (real_of_num (NUMERAL _0))))) (∀ (λ x : El _132718, (⇒ ((@IN _132718) x s) (= (f x) (real_of_num (NUMERAL _0)))))))))));
