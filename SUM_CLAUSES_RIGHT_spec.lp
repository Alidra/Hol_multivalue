require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7226365 : Prf (∀ (λ f : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (∧ (< (NUMERAL _0) n) (<= m n)) (= ((@sum num) (… m n) f) (real_add ((@sum num) (… m (- n (NUMERAL (BIT1 _0)))) f) (f n))))))))));
