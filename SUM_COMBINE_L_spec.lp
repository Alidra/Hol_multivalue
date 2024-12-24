require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7260931 : Prf (∀ (λ f : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (⇒ (∧ (< (NUMERAL _0) n) (∧ (<= m n) (<= n (+ p (NUMERAL (BIT1 _0)))))) (= (real_add ((@sum num) (… m (- n (NUMERAL (BIT1 _0)))) f) ((@sum num) (… n p) f)) ((@sum num) (… m p) f)))))))))));
