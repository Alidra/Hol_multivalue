require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7052037 : Prf (∀ (λ f : El (fun num num), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (<= m n) (= ((@nsum num) (… m n) f) (+ (f m) ((@nsum num) (… (+ m (NUMERAL (BIT1 _0))) n) f))))))))));
