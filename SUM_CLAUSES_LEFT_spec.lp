require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7226008 : Prf (∀ (λ f : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (<= m n) (= ((@sum num) (… m n) f) (real_add (f m) ((@sum num) (… (+ m (NUMERAL (BIT1 _0))) n) f))))))))));
