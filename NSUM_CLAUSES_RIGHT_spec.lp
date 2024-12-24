require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7052394 : Prf (∀ (λ f : El (fun num num), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ (< (NUMERAL _0) n) (<= m n)) (= ((@nsum num) (… m n) f) (+ ((@nsum num) (… m (- n (NUMERAL (BIT1 _0)))) f) (f n))))))))));
