require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7047063 : Prf (∀ (λ f : El (fun num num), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (< n m) (= ((@nsum num) (… m n) f) (NUMERAL _0)))))))));
