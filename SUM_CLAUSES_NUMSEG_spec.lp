require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7221724 (f : El (fun num real)) : Prf (∧ (∀ (λ m : El num, (= ((@sum num) (… m (NUMERAL _0)) f) ((@COND real) (= m (NUMERAL _0)) (f (NUMERAL _0)) (real_of_num (NUMERAL _0)))))) (∀ (λ m : El num, (∀ (λ n : El num, (= ((@sum num) (… m (SUC n)) f) ((@COND real) (<= m (SUC n)) (real_add ((@sum num) (… m n) f) (f (SUC n))) ((@sum num) (… m n) f))))))));
