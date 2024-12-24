require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7044962 : Prf (∀ (λ f : El (fun num num), (∀ (λ m : El num, (∀ (λ n : El num, (= (= ((@nsum num) (… m n) f) (NUMERAL _0)) (∀ (λ i : El num, (⇒ (∧ (<= m i) (<= i n)) (= (f i) (NUMERAL _0))))))))))));
