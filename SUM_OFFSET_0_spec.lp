require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7223337 : Prf (∀ (λ f : El (fun num real), (∀ (λ m : El num, (∀ (λ n : El num, (⇒ (<= m n) (= ((@sum num) (… m n) f) ((@sum num) (… (NUMERAL _0) (- n m)) (λ i : El num, (f (+ i m))))))))))));
