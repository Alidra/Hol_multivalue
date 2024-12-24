require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem163281 : Prf (= (⇒ (¬ (∀ (λ m : El num, (∀ (λ n : El num, (= (< (MOD m n) n) (¬ (= n (NUMERAL _0))))))))) F) (∀ (λ m : El num, (∀ (λ n : El num, (= (< (MOD m n) n) (¬ (= n (NUMERAL _0)))))))));
