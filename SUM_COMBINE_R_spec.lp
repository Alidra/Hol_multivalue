require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7244018 : Prf (∀ (λ f : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (∀ (λ p : El num, (⇒ (∧ (<= m (+ n (NUMERAL (BIT1 _0)))) (<= n p)) (= (real_add ((@sum num) (… m n) f) ((@sum num) (… (+ n (NUMERAL (BIT1 _0))) p) f)) ((@sum num) (… m p) f)))))))))));
